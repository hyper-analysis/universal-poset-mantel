from itertools import combinations, product


RANK = (0, 0, 1, 1, 2, 2)
BY_RANK = (0b000011, 0b001100, 0b110000)
EDGES = tuple((x, y) for x, y in combinations(range(len(RANK)), 2) if RANK[x] != RANK[y])
TRIPLES = tuple(product(range(2), range(2, 4), range(4, 6)))


def triangle_free_graphs():
    for pattern in range(1 << len(EDGES)):
        rows = [0] * len(RANK)
        for bit, (x, y) in enumerate(EDGES):
            if pattern >> bit & 1:
                rows[x] |= 1 << y
                rows[y] |= 1 << x
        if all(not (rows[x] >> y & 1 and rows[x] & rows[y]) for x, y in EDGES):
            yield tuple(rows)


def cut_readings(cut):
    readings = [0] * len(RANK)
    defaults = [0] * len(RANK)
    for x, y in EDGES:
        if (cut >> x & 1) == (cut >> y & 1):
            defaults[x] |= 1 << y
            defaults[y] |= 1 << x
        elif (x + y) % 2:
            readings[x] |= 1 << y
        else:
            readings[y] |= 1 << x
    return tuple(a | b for a, b in zip(readings, defaults)), defaults


def below(reads, x, x_bits, y, y_bits):
    all_positive = not (reads[x] & ~x_bits & (1 << y) or reads[y] & ~y_bits & (1 << x))
    third = 3 - RANK[x] - RANK[y]
    shared = bool(x_bits & y_bits & BY_RANK[third])
    if RANK[y] - RANK[x] == 2:
        return not all_positive or shared
    return all_positive and not shared


def slot_labels(reads, default_pairs, graph):
    for x, mask in enumerate(reads):
        labels = []
        for bits in range(1 << len(RANK)):
            if bits & ~mask:
                continue
            if ((bits ^ graph[x]) & default_pairs[x]).bit_count() <= 1:
                labels.append(bits)
        yield labels


def main():
    targets = tuple(triangle_free_graphs())
    embeddings = 0
    chains = 0
    # Fix the last slot on one side to enumerate cuts up to complementation.
    for cut in range(1 << (len(RANK) - 1)):
        reads, default_pairs = cut_readings(cut)
        for graph in targets:
            labels = tuple(row & mask for row, mask in zip(graph, reads))
            for x, y in EDGES:
                present = bool(graph[x] >> y & 1)
                expected = present != (RANK[y] - RANK[x] == 2)
                assert below(reads, x, labels[x], y, labels[y]) == expected
            embeddings += 1
        for i in range(24):
            graph = targets[(17 * i + 31 * cut) % len(targets)]
            labels = tuple(slot_labels(reads, default_pairs, graph))
            for x, y, z in TRIPLES:
                for x_bits, y_bits in product(labels[x], labels[y]):
                    if not below(reads, x, x_bits, y, y_bits):
                        continue
                    for z_bits in labels[z]:
                        if below(reads, y, y_bits, z, z_bits):
                            assert below(reads, x, x_bits, z, z_bits)
                            chains += 1
    print(f'{embeddings:,} induced embeddings across {len(targets):,} signed targets')
    print(f'{chains:,} two-step chains on arbitrary labels')


if __name__ == '__main__':
    main()
