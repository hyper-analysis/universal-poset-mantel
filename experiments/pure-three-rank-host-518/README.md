# Projecting middle profiles onto the selected outer vertices

This refines the 524-vertex pure three-rank host for profile (4, 8, 4). The starting host has 32 outer labels and 492 middle copies. Six certified deletions give a 518-vertex host. The relation and all outer labels stay the same when a middle copy is deleted. Each successful deletion is certified for every pure input of this profile, including connected inputs.

## Exact embedding rule

Fix an outer relation R and an assignment of its lower and upper vertices to host slots. The selected eight outer labels are determined by the owned bits of R. For each stored middle profile (D, U), compute its actual neighbors among those eight labels using the host comparison rule. The observed profile can be smaller than (D, U). Distinct stored profiles with the same observed pair give disjoint pools of copies whose capacities add. For this placement, a target embeds exactly when every demanded observed profile has enough copies. All selected outer comparisons already agree with R, and the middle rank is an antichain.

On the 524-vertex baseline, 178 of the 179 outer-relation representatives have at least one nonempty pool with two different contributing profiles. For relation 60855, stored profile (9, 6) has one copy, and 54 middle vertices induce that pair on the selected outer labels. The new embedding routine first tries nominal capacities and then tries the projected pools.

## Deletion proof

The starting capacity vector is verified by the unchanged nominal audit in zero.cpp. For each proposed deletion, the projected audit uses the previous certified host as its premise.

1. Enumerate the 179 outer-relation orbits. For each representative, consider all 576 outer slot permutations and compute projected capacities.
2. If a deletion creates a new failure, consider a placement that worked before it. A middle demand must equal the lost pool's previous capacity at that placement. Collect those demands as seeds.
3. For each seed, branch over further demands whose intersections leave fewer possible placements. If a failing multiset exists, it has a subcollection that eliminates all placements and uses at most eight middle vertices. The branch over repeated demands can omit demands that fail to shrink the placement set. The singleton branch chooses a surviving placement and tries every currently unused singleton demand it cannot support.
4. The union of the demanded rectangles must reach R. For a partial failure, the minimum number of rectangles that cover the missing edges is computed by memoized search over maximal rectangles within R. If it fits within the remaining budget, a failing input can be completed to eight middle vertices. Adding copies cannot restore any eliminated placement.
5. The stabilizer of R permutes the seeds, and pointwise stabilizers of selected profiles reduce later branches. These symmetries act on the target names only, leaving the existence of a placement invariant. Repeated demands are visited in decreasing multiplicity and increasing profile index at equal multiplicity.

The proof ranges over symbolic demand constraints and relation orbits. It does not generate a catalog of target posets. The deletion loop gives an upper bound.

## Replay

Requires Python 3.10+ and a C++20 compiler. Start with capacities.txt and pass the deletion masks in their verified order. The packed mask uses the lower subset in the low nibble and the upper subset in the high nibble.

```sh
python3 verify.py 26 50 24 29 68 70 --output improved-518.txt
python3 host.py improved-518.txt --trials 2000 --graph host-518.json
```

The second command also regenerates the supplied host JSON with every strict comparison.

The Python replay checks host transitivity and induced embeddings for sampled inputs and representatives of all outer-relation orbits. The C++ audit establishes universal coverage for each deletion.
