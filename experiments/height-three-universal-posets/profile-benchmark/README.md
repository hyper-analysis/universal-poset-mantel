# A finite height-three benchmark

The target family consists of all 16-element posets with longest-chain rank sizes `(4, 8, 4)`. Ranks are numbered from the bottom. These targets can have skipping covers, repeated neighborhoods, and isolated bottom vertices.

## Profile host and certification

An 8-element middle multiset records profiles `(D, U)`. Each down mask `D` is nonempty. The upper masks can be empty individually, and their union is the entire top rank. This describes exactly the adjacent blocks of the target family. The outer comparison matrix may be any superset of the union of the rectangles `D × U`.

Every outer pair has one fixed owner. Each of the eight outer slots owns two bits, giving 32 outer labels in total. Store the target's full outer comparison matrix in those labels. The two adjacent blocks use the stored middle profiles. For a bottom or top label to compare to a middle label, the relevant profile bit must be set, and all outer comparisons in the middle rectangle owned by that endpoint must be set. Thus every two-step chain has its outer comparison. Any target placement respecting the middle capacities induces the full target because each of its rectangles is contained in its outer matrix.

`capacities.txt` has 240 nonnegative integers, ordered by upper mask from 0 through 15, then down mask from 1 through 15. The exact audit searches for a multiset of at most eight demands that excludes all 576 independent relabelings of the two outer ranks. Partial obstructions of length at most seven can be padded with the full profile. A length-eight obstruction must reach all four top slots. Repeated demands are ordered by decreasing multiplicity. Singleton demands branch on ways to eliminate one still-surviving permutation. Demands that remove no surviving permutation can be omitted, since a shorter obstruction admits the same padding argument. Run the one-argument verifier to check the supplied table without symmetry pruning.

## Signed cuts

The signed graph has edges for adjacent-rank comparisons and for bottom-to-top incomparabilities. Each cut template includes all cross-rank pairs crossing its cut as variable edges. It uses zero defaults for the other pairs and allows up to `d` positive deviations per slot. Each variable bit is read at one endpoint, and deviations are readable at both endpoints. This uses the decoder in [Induced-universal posets of height three](../../../math/height-three-universal-posets.md).

Let `q[x]` be the number of off-template cross-rank pairs at slot `x`, and let `r[x]` be the number of variable reads assigned to it. Its label count is `2^r[x] · sum(C(q[x], j), j = 0..min(q[x], d))`. The probe minimizes the sum of these counts by assigning edges via augmenting paths. Once a read is added, an augmenting path can transfer existing reads to their other endpoints. The only load increase occurs at the final slot, with marginal cost equal to its current label count.

The probe exhausts all 32,768 cuts up to flipping sides. For each target it reports the smallest compatible component in this family. A shared host counts the vertices of the selected components once each. The fixed cut putting the middle rank on one side is a 1,024-vertex shared construction for the entire target family. Its maximum deviation degree is four. Eight outer slots can read two variable bits each and eight middle slots can read six each, for 64 labels per slot.

The seeded sample has 250 targets each from sparse, mixed, dense, and repeated-profile families. Replays compare every pair in a profile embedding and exhaustively check the profile host's two-step paths. Cut component sizes and shared sample coverage use the designated cut encoding.

## Reproduce

```sh
g++ -O3 -std=c++20 -Wall -Wextra audit.cpp -o audit
./audit capacities.txt
g++ -O3 -std=c++20 -Wall -Wextra cuts.cpp -o cuts
python3 benchmark.py capacities.txt
```

The audit also accepts an optional second path. With that argument, it greedily repairs the input table and writes its candidate table to the second path. Run the one-argument audit on a repaired table to verify it.

See `results.txt` for the supplied table's verification and replay results.
