"""Implicit height-three host and induced embedding for pure profile (4, 8, 4)."""
import argparse
import json
import random
from collections import Counter, defaultdict
from pathlib import Path

from conditioned import MIDDLE, PERMS, PROFILES, SIDE, canonical_relations, slots

MASK = (1 << SIDE) - 1


def read_capacities(path):
    values = [int(value) for value in Path(path).read_text().split()]
    if len(values) != len(PROFILES) or any(not 0 <= value <= MIDDLE for value in values):
        raise ValueError('expected 225 capacities in the range 0 through 8')
    return dict(zip(PROFILES, values, strict=True))


def permute(mask, order):
    return sum(1 << order[i] for i in slots(mask, SIDE))


class Host:
    def __init__(self, capacity, endpoints=None):
        self.capacity = capacity
        self.owned_by_row = (3, 12, 3, 12)
        self.owned_by_column = tuple(sum(1 << i for i, row in enumerate(self.owned_by_row)
                                         if not (row >> j & 1)) for j in range(SIDE))

        ownership = self.owned_by_row + self.owned_by_column
        self.endpoints = tuple(frozenset(bits for bits in range(1 << SIDE)
                                         if bits & owned == bits and
                                         (endpoints is None or endpoints[slot] >> bits & 1))
                               for slot, owned in enumerate(ownership))

    def vertices(self):
        endpoints = [(2 * side, i, bits) for side in range(2) for i in range(SIDE)
                     for bits in sorted(self.endpoints[side * SIDE + i])]
        middle = [(1, down, up, copy) for (down, up), cap in self.capacity.items()
                  for copy in range(cap)]
        return endpoints + middle

    def below(self, x, y):
        if x[0] == 0 and y[0] == 2:
            return bool(x[2] >> y[1] & 1 if self.owned_by_row[x[1]] >> y[1] & 1
                        else y[2] >> x[1] & 1)
        if x[0] == 0 and y[0] == 1:
            return bool(y[1] >> x[1] & 1) and y[2] & self.owned_by_row[x[1]] & ~x[2] == 0
        if x[0] == 1 and y[0] == 2:
            return bool(x[2] >> y[1] & 1) and x[1] & self.owned_by_column[y[1]] & ~y[2] == 0
        return False

    def embed(self, profiles):
        if (len(profiles) != MIDDLE or any(pair not in self.capacity for pair in profiles)
                or not is_pure(profiles)):
            raise ValueError('expected eight nonempty profile pairs covering both outer ranks')
        for left in PERMS:
            for right in PERMS:
                mapped = [(permute(down, left), permute(up, right)) for down, up in profiles]
                weights = Counter(mapped)
                embedding = self.embed_with_relabeling(left, right, mapped)
                if not self.has_endpoints(embedding):
                    continue
                if all(weights[pair] <= self.capacity[pair] for pair in weights):
                    return embedding
                lower, upper = embedding[:SIDE], embedding[-SIDE:]
                pools = defaultdict(list)
                for (down, up), cap in self.capacity.items():
                    if not cap:
                        continue
                    middle = (1, down, up, 0)
                    visible_down = sum(1 << v[1] for v in lower if self.below(v, middle))
                    visible_up = sum(1 << v[1] for v in upper if self.below(middle, v))
                    if (visible_down, visible_up) in weights:
                        pools[visible_down, visible_up].extend((1, down, up, k) for k in range(cap))
                if all(len(pools[pair]) >= count for pair, count in weights.items()):
                    return lower + [pools[pair].pop() for pair in mapped] + upper
        raise ValueError('no outer-rank relabeling admits the given profiles')

    def has_endpoints(self, embedding):
        return all(bits in self.endpoints[rank // 2 * SIDE + slot]
                   for rank, slot, bits in embedding[:SIDE] + embedding[-SIDE:])

    def embed_with_relabeling(self, left, right, mapped):
        rows = [0] * SIDE
        columns = [0] * SIDE
        middle = []
        used = Counter()
        for down, up in mapped:
            middle.append((1, down, up, used[down, up]))
            used[down, up] += 1
            for i in slots(down, SIDE):
                rows[i] |= up
            for j in slots(up, SIDE):
                columns[j] |= down
        lower = [(0, i, rows[i] & self.owned_by_row[i]) for i in left]
        upper = [(2, j, columns[j] & self.owned_by_column[j]) for j in right]
        return lower + middle + upper


def is_pure(profiles):
    lower = upper = 0
    for down, up in profiles:
        lower |= down
        upper |= up
    return lower == upper == MASK


def target_order(profiles):
    order = set()
    for k, (down, up) in enumerate(profiles, SIDE):
        bottoms = slots(down, SIDE)
        tops = [SIDE + MIDDLE + j for j in slots(up, SIDE)]
        order.update((i, k) for i in bottoms)
        order.update((k, j) for j in tops)
        order.update((i, j) for i in bottoms for j in tops)
    return order


def check(host, trials):
    vertices = host.vertices()
    assert len(set(vertices)) == len(vertices)
    vertex_set = set(vertices)
    upper = [[j for j, y in enumerate(vertices) if host.below(x, y)] for x in vertices]
    masks = [sum(1 << j for j in row) for row in upper]
    for i, row in enumerate(upper):
        assert i not in row
        assert all(masks[j] & masks[i] == masks[j] for j in row)
    randomizer = random.Random(41)
    cases = []
    relations = canonical_relations()
    for relation in relations:
        profiles = [(1 << i, relation >> (SIDE * i) & MASK) for i in range(SIDE)]
        cases.append(profiles + [profiles[0]] * (MIDDLE - len(profiles)))
    for _ in range(trials):
        profiles = randomizer.choices(PROFILES, k=MIDDLE)
        if is_pure(profiles):
            cases.append(profiles)
    for profiles in cases:
        embedding = host.embed(profiles)
        assert len(set(embedding)) == len(embedding) and set(embedding) <= vertex_set
        induced = {(i, j) for i, x in enumerate(embedding)
                   for j, y in enumerate(embedding) if host.below(x, y)}
        assert induced == target_order(profiles)
    print(f'{len(vertices)}-vertex host is transitive. Replayed {len(cases)} embeddings, '
          f'including one for each of the {len(relations)} outer-relation orbits.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capacities')
    parser.add_argument('--endpoints', type=Path, help='allowed label masks for the eight outer slots')
    parser.add_argument('--trials', type=int, default=500)
    parser.add_argument('--graph', type=Path, help='export every strict comparison to JSON')
    args = parser.parse_args()
    endpoints = [int(value) for value in args.endpoints.read_text().split()] if args.endpoints else None
    host = Host(read_capacities(args.capacities), endpoints)
    check(host, args.trials)
    if args.graph:
        vertices = host.vertices()
        data = {'vertices': vertices, 'below': [(i, j) for i, x in enumerate(vertices)
                                                 for j, y in enumerate(vertices) if host.below(x, y)]}
        args.graph.write_text(json.dumps(data, separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
