import argparse
from collections import Counter
from itertools import permutations
from pathlib import Path
import random
from statistics import median
import subprocess


MASK = 15
MIDDLE = 8
ORDERS = tuple(permutations(range(4)))
REMAP = [
    tuple(sum(1 << order[i] for i in range(4) if mask >> i & 1) for mask in range(16))
    for order in ORDERS
]
PROFILES = tuple((down, up) for up in range(16) for down in range(1, 16))
OWNED_LOWER = (3, 12, 3, 12)
OWNED_UPPER = tuple(
    sum(1 << i for i, bits in enumerate(OWNED_LOWER) if not bits >> j & 1)
    for j in range(4)
)


def below(x, y):
    if (x[0], y[0]) == (0, 2):
        return bool(x[2] >> y[1] & 1 if OWNED_LOWER[x[1]] >> y[1] & 1 else y[2] >> x[1] & 1)
    if (x[0], y[0]) == (0, 1):
        return bool(y[1] >> x[1] & 1) and y[2] & OWNED_LOWER[x[1]] & ~x[2] == 0
    if (x[0], y[0]) == (1, 2):
        return bool(x[2] >> y[1] & 1) and x[1] & OWNED_UPPER[y[1]] & ~y[2] == 0
    return False


def vertices(capacity):
    lower = [(0, i, bits, 0) for i, owned in enumerate(OWNED_LOWER)
             for bits in range(16) if bits & owned == bits]
    upper = [(2, i, bits, 0) for i, owned in enumerate(OWNED_UPPER)
             for bits in range(16) if bits & owned == bits]
    middle = [(1, down, up, repeat) for (down, up), copies in capacity.items()
              for repeat in range(copies)]
    return lower, middle, upper


def covers_top(profiles):
    top = 0
    for _, up in profiles:
        top |= up
    return top == MASK


def embed(capacity, profiles, outer):
    for i, left in enumerate(REMAP):
        for j, right in enumerate(REMAP):
            mapped = [(left[down], right[up]) for down, up in profiles]
            if any(count > capacity[p] for p, count in Counter(mapped).items()):
                continue
            order_a, order_c = ORDERS[i], ORDERS[j]
            rows = {order_a[x]: right[row] for x, row in enumerate(outer)}
            columns = {c: sum(1 << a for a, row in rows.items() if row >> c & 1) for c in order_c}
            lower = [(0, a, rows[a] & OWNED_LOWER[a], 0) for a in order_a]
            upper = [(2, c, columns[c] & OWNED_UPPER[c], 0) for c in order_c]
            used = Counter()
            mids = []
            for down, up in mapped:
                mids.append((1, down, up, used[down, up]))
                used[down, up] += 1
            return lower + mids + upper
    raise ValueError(f'no induced embedding for profiles {profiles}')


def target(profiles, outer):
    adjacent = {(i, 4+k) for k, (d, _) in enumerate(profiles) for i in range(4) if d >> i & 1}
    adjacent.update((4+k, 12+j) for k, (_, u) in enumerate(profiles) for j in range(4) if u >> j & 1)
    outer_pairs = {(i, 12+j) for i, row in enumerate(outer) for j in range(4) if row >> j & 1}
    strict = adjacent | outer_pairs
    signed = [0]*16
    for i in range(12):
        for j in range(4 if i < 4 else 12, 16):
            present = (i, j) not in outer_pairs if i < 4 and j >= 12 else (i, j) in adjacent
            if present:
                signed[i] |= 1 << j
                signed[j] |= 1 << i
    assert all(signed[i] & signed[j] == 0 for i in range(16) for j in range(16) if signed[i] >> j & 1)
    return strict, signed


def cases(count):
    rng = random.Random(41)

    def mask(p):
        return sum(1 << i for i in range(4) if rng.random() < p)

    for kind, p, skip in [('sparse', .25, .12), ('mixed', .5, .4), ('dense', .78, .75),
                          ('repeated', .45, .25)]:
        for _ in range(count):
            while True:
                profiles = [(mask(p) or (1 << rng.randrange(4)), mask(p)) for _ in range(MIDDLE)]
                if kind == 'repeated':
                    down = rng.randrange(1, 16)
                    profile = (down, 15 if rng.random() < .5 else 0)
                    copies = rng.randrange(5, 9)
                    profiles[:copies] = [profile]*copies
                if covers_top(profiles):
                    break
            outer = [mask(skip) for _ in range(4)]
            for down, up in profiles:
                for i in range(4):
                    if down >> i & 1:
                        outer[i] |= up
            yield kind, profiles, outer


def best_shared_templates(costs, degrees):
    full = (1 << len(degrees)) - 1
    by_coverage = {}
    for shape, row in enumerate(costs):
        for cap, cost in enumerate(row):
            covered = sum(1 << i for i, demand in enumerate(degrees) if demand[shape] <= cap)
            if covered:
                by_coverage[covered] = min(cost, by_coverage.get(covered, cost))
    single = by_coverage[full]
    candidates = sorted((cost, covered) for covered, cost in by_coverage.items() if cost < single)
    best = single
    for i, (cost, covered) in enumerate(candidates):
        for other_cost, other_covered in candidates[i+1:]:
            if cost + other_cost >= best:
                break
            if covered | other_covered == full:
                best = cost + other_cost
    return single, best


def main():
    options = argparse.ArgumentParser()
    options.add_argument('capacities', type=Path)
    options.add_argument('--cut-probe', default='./cuts')
    options.add_argument('--per-family', type=int, default=250)
    args = options.parse_args()
    values = [int(value) for value in args.capacities.read_text().split()]
    assert len(values) == len(PROFILES) and all(0 <= value <= MIDDLE for value in values)
    capacity = dict(zip(PROFILES, values))
    lower, mid, upper = vertices(capacity)
    universe = set(lower + mid + upper)
    assert len(universe) == 32 + sum(values)
    for m in mid:
        preds = [a for a in lower if below(a, m)]
        succs = [c for c in upper if below(m, c)]
        assert all(below(a, c) for a in preds for c in succs)

    data = []
    for kind, profiles, outer in cases(args.per_family):
        embedding = embed(capacity, profiles, outer)
        assert len(set(embedding)) == 16 and set(embedding) <= universe
        strict, signed = target(profiles, outer)
        induced = {(i, j) for i, x in enumerate(embedding)
                   for j, y in enumerate(embedding) if below(x, y)}
        assert induced == strict
        data.append(kind + ' ' + ' '.join(map(str, signed)))

    result = subprocess.run([args.cut_probe], input='\n'.join(data) + '\n',
                            text=True, check=True, capture_output=True)
    rows = result.stdout.splitlines()
    costs = [list(map(int, row.split())) for row in rows[:113]]
    assert len(costs) == 113 and all(len(row) == 13 for row in costs)
    outcomes = {}
    degrees = []
    for row in rows[113:]:
        kind, best, fixed, *demand = row.split()
        outcomes.setdefault(kind, []).append((int(best), int(fixed)))
        degrees.append(tuple(map(int, demand)))
    assert sum(map(len, outcomes.values())) == len(data)
    print(f'{len(universe)} profile-host vertices, {len(data)} independently replayed embeddings')
    print('family     cases  best cut min/median/max    floor cut min/median/max')
    for kind, observations in outcomes.items():
        best, fixed = zip(*observations)
        print(f'{kind:<10} {len(best):>5}  {min(best):>4}/{median(best):>5g}/{max(best):<4}'
              f'             {min(fixed):>4}/{median(fixed):>5g}/{max(fixed)}')
    best = [a for cases_for_kind in outcomes.values() for a, _ in cases_for_kind]
    print(f'Best-cut component across all cases: {min(best)}/{median(best):g}/{max(best)}; '
          f'{sum(x < len(universe) for x in best)} smaller than the shared profile host.')
    single, pair = best_shared_templates(costs, degrees)
    print(f'Entire sample: best single cut component = {single}, '
          f'best union of at most two cut components = {pair}.')


if __name__ == '__main__':
    main()
