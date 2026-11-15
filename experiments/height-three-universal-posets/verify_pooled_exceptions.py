from itertools import product


BASE_RANKS = (0, 1, 1, 2)
BASE_ORDER = {(0, 1), (1, 3), (0, 3)}


def subsets(mask):
    subset = mask
    while True:
        yield subset
        if subset == 0:
            break
        subset = (subset - 1) & mask


def exception_ranks(counts):
    return tuple(rank for rank, count in enumerate(counts) for _ in range(count))


def labels_for(counts):
    ranks = exception_ranks(counts)
    labels = []
    for rank in range(3):
        lower = sum(1 << i for i, r in enumerate(ranks) if r < rank)
        upper = sum(1 << i for i, r in enumerate(ranks) if r > rank)
        base_vertices = [(v, 0) for v, r in enumerate(BASE_RANKS) if r == rank]
        exception_vertices = [(-1, 1 << i) for i, r in enumerate(ranks) if r == rank]
        labels.append(tuple((rank, base, down | self_bit, up | self_bit)
                            for base, self_bit in base_vertices + exception_vertices
                            for down, up in product(subsets(lower), subsets(upper))))
    return labels


def below(left, right):
    left_rank, left_base, left_down, left_up = left
    right_rank, right_base, right_down, right_up = right
    return bool(left_rank < right_rank
                and not left_down & ~right_down and not right_up & ~left_up
                and ((left_base, right_base) in BASE_ORDER or left_up & right_down))


def transitive(vertices, edges):
    successors = {x: set() for x in vertices}
    for x, y in edges:
        successors[x].add(y)
    return all(successors[y] <= successors[x] for x, y in edges)


def verify_target_embeddings(counts, labels):
    ranks = BASE_RANKS + exception_ranks(counts)
    vertices = tuple(range(len(ranks)))
    first_exception = len(BASE_RANKS)
    variable = [(x, y) for x, y in product(vertices, repeat=2)
                if ranks[x] < ranks[y] and max(x, y) >= first_exception]
    checked = 0
    for bits in product((0, 1), repeat=len(variable)):
        edges = BASE_ORDER | {edge for bit, edge in zip(bits, variable) if bit}
        if not transitive(vertices, edges):
            continue
        chosen = []
        for v in vertices:
            down = up = 0
            for i in range(first_exception, len(ranks)):
                bit = 1 << (i - first_exception)
                if v == i or (i, v) in edges:
                    down |= bit
                if v == i or (v, i) in edges:
                    up |= bit
            label = (ranks[v], v if v < first_exception else -1, down, up)
            assert label in labels[ranks[v]]
            chosen.append(label)
        assert len(set(chosen)) == len(vertices)
        assert {(x, y) for x, y in product(vertices, repeat=2)
                if below(chosen[x], chosen[y])} == edges
        checked += 1
    return checked


def verify_gluing(pool_rank, lifts):
    vertices = set()
    edges = set()
    components = []
    for tag, labels in enumerate(lifts):
        image = {(rank, -1 if rank == pool_rank else tag, i): label
                 for rank in range(3) for i, label in enumerate(labels[rank])}
        original = {(x, y) for x, a in image.items() for y, b in image.items() if below(a, b)}
        vertices.update(image)
        edges.update(original)
        components.append((image, original))
    if pool_rank == 1:
        bottom = [v for v in vertices if v[0] == 0]
        top = [v for v in vertices if v[0] == 2]
        edges.update((x, y) for x, y in product(bottom, top) if x[1] != y[1])
    assert transitive(vertices, edges)
    for image, original in components:
        assert {(x, y) for x, y in product(image, repeat=2) if (x, y) in edges} == original
    return len(components)


def main():
    checked = 0
    components = 0
    for k in range(4):
        groups = [[], [], []]
        for a in range(k + 1):
            for m in range(k - a + 1):
                counts = (a, m, k - a - m)
                labels = labels_for(counts)
                pool_rank = min(range(3), key=counts.__getitem__)
                groups[pool_rank].append(labels)
                checked += verify_target_embeddings(counts, labels)
        for pool_rank, lifts in enumerate(groups):
            components += verify_gluing(pool_rank, lifts)
    print(f'{checked:,} induced exception embeddings and {components} pooled components')


if __name__ == '__main__':
    main()
