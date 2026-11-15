from itertools import product
from math import lcm

from verify_cut_defaults import EDGES, RANK, triangle_free_graphs


def below(x, y, outer, reads, positive):
    if x == y:
        return outer
    signed = (not (reads[x] >> y & 1) or bool(positive[x] >> y & 1)) and (
        not (reads[y] >> x & 1) or bool(positive[y] >> x & 1)
    )
    shared = bool(positive[x] & positive[y])
    if outer:
        return not signed or shared
    return signed and not shared


def check_reader_triangles():
    pairs = ((0, 1), (1, 2), (0, 2))
    checked = 0
    for choices in product((-1, 0, 1), repeat=3):
        reads = [0] * 3
        for (x, y), choice in zip(pairs, choices):
            if choice >= 0:
                reads[x] |= 1 << y
            if choice <= 0:
                reads[y] |= 1 << x
        has_cycle = choices in ((1, 1, -1), (-1, -1, 1))
        failed = False
        labels = [tuple(s for s in range(8) if s & ~mask == 0) for mask in reads]
        for bits in product(*labels):
            if (below(0, 1, False, reads, bits)
                    and below(1, 2, False, reads, bits)
                    and not below(0, 2, True, reads, bits)):
                failed = True
            checked += 1
        assert failed == has_cycle
    return checked


def check_rank_independent_embeddings():
    reads = [sum(1 << y for y in range(x + 1, len(RANK))) for x in range(len(RANK))]
    checked = 0
    for graph in triangle_free_graphs():
        positive = tuple(row & mask for row, mask in zip(graph, reads))
        for x, y in EDGES:
            outer = RANK[y] - RANK[x] == 2
            assert below(x, y, outer, reads, positive) == (bool(graph[x] >> y & 1) != outer)
        checked += 1
    return checked


def component_counts(slots, size):
    if size == 1:
        yield (slots,)
        return
    for count in range(slots // size + 1):
        for smaller in component_counts(slots - count * size, size - 1):
            yield (*smaller, count)


def check_block_packing():
    checked = 0
    for cutoff in range(1, 7):
        width = lcm(*range(1, cutoff + 1))
        for slots in range(41):
            required = max(0, slots // width - (cutoff - 1))
            assert 0 <= slots - required * width < cutoff * width
            for counts in component_counts(slots, cutoff):
                complete = sum(count // (width // i) for i, count in enumerate(counts, 1))
                assert complete >= required
                checked += 1
    return checked


if __name__ == '__main__':
    print(f'{check_reader_triangles():,} ownership-triangle label assignments')
    print(f'{check_rank_independent_embeddings():,} induced rank-independent embeddings')
    print(f'{check_block_packing():,} component size profiles packed')
