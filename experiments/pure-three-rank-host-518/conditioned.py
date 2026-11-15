from itertools import permutations

SIDE = 4
MIDDLE = 8
FULL = (1 << (SIDE * SIDE)) - 1
SUBSETS = range(1, 1 << SIDE)
PROFILES = [(left, right) for right in SUBSETS for left in SUBSETS]
PERMS = tuple(permutations(range(SIDE)))


def slots(mask, size):
    return [i for i in range(size) if mask >> i & 1]


def rectangle(left, right):
    return sum(right << (SIDE * i) for i in slots(left, SIDE))


RECTANGLES = [rectangle(*pair) for pair in PROFILES]


def canonical_relations():
    """Represent each relation up to independent permutations of its two ranks."""
    column_permutations = [
        [sum(1 << p[i] for i in slots(mask, SIDE)) for mask in range(1 << SIDE)]
        for p in PERMS
    ]
    relations = set()
    for relation in range(1, FULL + 1):
        rows = [(relation >> (SIDE * i)) & 15 for i in range(SIDE)]
        if 0 in rows or rows[0] | rows[1] | rows[2] | rows[3] != 15:
            continue
        relations.add(min(sum(row << (SIDE * i) for i, row in enumerate(
            sorted(column_perm[row] for row in rows))) for column_perm in column_permutations))
    return sorted(relations)


def capacities(relation):
    """Exact middle capacities when the labeled outer relation is fixed.

    Each rectangle can be extended inside the relation to an inclusion-maximal
    rectangle. It suffices to use maximal rectangles when minimizing the number
    of rectangles needed to cover the missing pairs.
    """
    allowed = [rect for rect in RECTANGLES if rect & relation == rect]
    maximal = [rect for rect in allowed
               if not any(rect != other and rect & other == rect for other in allowed)]
    dist = {0: 0}
    frontier = {0}
    depth = 0
    while frontier:
        frontier = {state | rect for state in frontier for rect in maximal} - dist.keys()
        depth += 1
        dist.update(dict.fromkeys(frontier, depth))
    return {rect: MIDDLE - min(cost for covered, cost in dist.items()
                              if covered | rect == relation) for rect in allowed}


def main():
    relations = canonical_relations()
    totals = []
    for relation in relations:
        caps = capacities(relation)
        totals.append((relation.bit_count(), sum(caps.values())))
    print(f'{len(relations)} outer-relation orbits')
    print(f'{sum(total for _, total in totals):,} middle vertices in separate pools')
    print(f'{sum(total + 2 * SIDE for _, total in totals):,} total vertices if disjoint')
    for edges in sorted(set(n for n, _ in totals)):
        counts = [total for n, total in totals if edges == n]
        print(f'{edges:2} pairs {len(counts):3} orbits {min(counts):4} min {max(counts):4} max')


if __name__ == '__main__':
    main()
