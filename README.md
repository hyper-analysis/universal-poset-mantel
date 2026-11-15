# Induced-universal posets of height three

Let $u_3(n)$ be the smallest size of a poset of height at most three containing
every $n$-element poset of height at most three as an induced subposet. The
Mantel–Hall construction and a counting lower bound give
$u_3(n)=2^{n/4+o(n)}$. The same leading exponent holds for connected targets
whose maximal chains all have three elements.

The construction encodes adjacent-rank comparisons and bottom-to-top
incomparabilities as edges of a triangle-free graph. Mantel's theorem and
Hall's theorem allocate the bits on a triangle-free template to its endpoints.
The decoder defines a transitive order on the whole label set, including
labels chosen from different targets.

## Proof and refinements

- [Typeset proof](math/height-three-mantel-hall-proof.pdf) and
  [LaTeX source](math/height-three-mantel-hall-proof.tex).
- [Extended proof notes](math/height-three-universal-posets.md) cover the
  rank-profile exponent, a quantitative sublinear term, cut templates, and
  exception pooling. The bipartite signed-graph case has an
  $O(2^{n/4})$ bound. A polynomial prefactor for the full height-three
  family remains open here.
- [Lean formalization](math/HeightThreeBound.lean) proves the asymptotic
  upper bound and the matching counting lower bounds for both target families.
  The file compiles with Lean and Mathlib v4.30.0.
- [Computational checks](experiments/height-three-universal-posets/README.md)
  cover the decoder and several of its refinements.

## Finite hosts for rank profile $(4,8,4)$

| Target family | Host vertices | Replay |
| --- | ---: | --- |
| All targets with these longest-chain ranks, including skipping covers | 657 | [Exact capacity audit and cut benchmark](experiments/height-three-universal-posets/profile-benchmark/README.md) |
| Pure three-rank targets, including connected targets | 518 | [Baseline audit and projected deletion verification](experiments/pure-three-rank-host-518/README.md) |

Both numbers are upper bounds for their indicated families.
