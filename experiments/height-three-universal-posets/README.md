# Computational checks for the Mantel–Hall construction

These programs check the signed decoder and particular refinements of the
construction in the [proof notes](../../math/height-three-universal-posets.md).

From this directory, run the decoder verifier with a C++17 compiler:

```sh
work=$(mktemp -d)
c++ -O3 -std=c++17 -Wall -Wextra -pedantic check_decoder.cpp -o "$work/check_decoder"
"$work/check_decoder"
```

The following scripts use Python's standard library:

```sh
python3 verify_cut_defaults.py
python3 verify_directed_readers.py
python3 verify_matching_slack.py
python3 verify_pooled_exceptions.py
```

The [fixed-profile benchmark](profile-benchmark/README.md) gives separate
instructions for reproducing its exact capacity audit and the cut comparison.
