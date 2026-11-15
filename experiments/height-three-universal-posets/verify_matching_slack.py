from fractions import Fraction
from math import ceil, log2

from verify_cut_defaults import RANK, triangle_free_graphs


def cyclic_load(blocks, width, columns):
    return [sum((j - i * width) % columns < width for i in range(blocks))
            for j in range(columns)]


def verify_matching_layouts():
    checked = 0
    pair_cost = log2(3)
    for p in range(1, 33):
        for q in range(1, 33):
            for matching_size in range(p // 2 + 1):
                singles = p - 2 * matching_size
                weight = singles + pair_cost * matching_size
                owned_by_left = ceil(weight * q / (weight + q))
                owned_by_right = q - owned_by_left
                single_load = cyclic_load(singles, owned_by_right, q)
                pair_load = cyclic_load(matching_size, owned_by_right, q)
                assert max(single_load) - min(single_load) <= 1
                assert max(pair_load) - min(pair_load) <= 1
                assert all(a + pair_cost * b <= owned_by_left + 1 + pair_cost
                           for a, b in zip(single_load, pair_load))
                checked += 1
    return checked


def edge_count(graph, subset):
    return sum((row & subset).bit_count() for i, row in enumerate(graph) if subset >> i & 1) // 2


def verify_mantel_reduction():
    checked = 0
    for graph in triangle_free_graphs():
        n = len(graph)
        all_slots = (1 << n) - 1
        edges = edge_count(graph, all_slots)
        for subset in range(1, 1 << n):
            width = subset.bit_count()
            counts = [sum((subset >> x) & 1 for x, rank in enumerate(RANK) if rank == r)
                      for r in range(3)]
            assert edge_count(graph, subset) <= max(a * (width - a) for a in counts)
        beta = max(Fraction(edge_count(graph, subset), subset.bit_count())
                   for subset in range(1, 1 << n))
        assert 4 * beta * beta <= edges
        left = max(graph, key=int.bit_count)
        right = all_slots ^ left
        possible_cross = left.bit_count() * right.bit_count()
        within = edge_count(graph, right)
        missing = possible_cross - (edges - within)
        deficit = Fraction(n * n, 4) - edges
        assert edge_count(graph, left) == 0
        assert within <= deficit
        assert missing <= 2 * deficit
        assert (left.bit_count() - Fraction(n, 2)) ** 2 <= deficit
        checked += 1
    return checked


if __name__ == '__main__':
    print(f'{verify_matching_layouts():,} cyclic read layouts')
    print(f'{verify_mantel_reduction():,} triangle-free Mantel reductions')
