"""Replay each deletion from the certified 524-vertex starting host."""
from argparse import ArgumentParser
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from conditioned import canonical_relations
from host import Host, check, read_capacities


def verify(deletions, output, trials):
    root = Path(__file__).resolve().parent
    baseline = root / 'capacities.txt'
    capacity = read_capacities(baseline)
    with TemporaryDirectory() as directory:
        working = Path(directory)
        zero = working / 'zero'
        projected = working / 'projection'
        for source, binary in [('zero.cpp', zero), ('projection.cpp', projected)]:
            run(['g++', '-std=c++20', '-O3', '-Wall', '-Wextra', root / source, '-o', binary], check=True)
        run([zero, baseline], check=True)
        relations = sorted(canonical_relations(), key=lambda r: (r != 65535, r.bit_count()))
        relation_file = working / 'relations.txt'
        relation_file.write_text(''.join(f'{r}\n' for r in relations))
        predecessor = working / 'predecessor.txt'
        for mask in deletions:
            pair = (mask & 15, mask >> 4)
            if capacity.get(pair, 0) <= 0:
                raise ValueError(f'profile {mask} has no copy to remove')
            predecessor.write_text(' '.join(map(str, capacity.values())) + '\n')
            run([projected, predecessor, relation_file, str(mask)], check=True)
            capacity[pair] -= 1
    check(Host(capacity), trials)
    if output:
        output.write_text(' '.join(map(str, capacity.values())) + '\n')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('deletions', nargs='+', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--trials', type=int, default=2000)
    args = parser.parse_args()
    verify(args.deletions, args.output, args.trials)
