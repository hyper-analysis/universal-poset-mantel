# Induced-universal posets of height three

[Typeset proof (PDF)](height-three-mantel-hall-proof.pdf) · [LaTeX source](height-three-mantel-hall-proof.tex)

**Theorem.** The minimum size of a height-at-most-three poset containing every $n$-element height-at-most-three poset as an induced subposet is $2^{n/4+o(n)}$. The same exponent holds if the targets are restricted to connected pure three-rank posets.

## Encode the three ranks by a triangle-free graph

Put a vertex on the rank given by the length of a longest chain ending there. Call the three ranks $A,M,C$. Empty ranks are allowed. Form a tripartite graph $G$ on the same vertices. On $A\times M$ and $M\times C$, a graph edge represents a comparison. On $A\times C$, a graph edge represents an incomparability.

A triangle is exactly a violation of $a<m<c\Rightarrow a<c$. Conversely, every triangle-free graph with these three fixed parts decodes to a poset. The outer pair can be comparable with or without a middle witness, so this encoding covers skipping covers.

## A decoder for one template

Fix a partition of $n$ slots into the three ranks and a triangle-free tripartite graph $H$ on those slots. Each cross-rank pair in $H$ is read at one designated endpoint. Every cross-rank pair outside $H$ is read at both endpoints. A label for slot $x$ records a set $S_x$ of slots where it reads a positive graph bit. For each cross-rank pair, order the labels by the following rules.

- For an outer label $x$ and a middle label $m$, the adjacent comparison holds if every designated reading of $xm$ is positive and $S_x\cap S_m$ has no slot on the third rank.
- For a bottom label $a$ and a top label $c$, declare $a<c$ if any designated reading of $ac$ is zero or $S_a\cap S_c$ contains a middle slot.

The order is strict and goes upward between ranks. Suppose $a<m<c$ holds for three arbitrary labels at distinct ranks. If all designated readings of $ac$ are positive, choose one endpoint $x\in\{a,c\}$ that reads that bit as positive and let $y$ be the other endpoint. If $m$ read $my$, the adjacent comparison $m,y$ would require a positive reading, which would put $y$ in $S_x\cap S_m$ and veto $x,m$. Thus $my\in H$ and $y$ alone reads it as positive. Now split on whether $ac\in H$.

- If $ac\in H$, it is read only by $x$. We already have $my\in H$. Triangle-freeness gives $mx\notin H$, so $mx$ is read as positive by $x$.
- If $ac\notin H$, both outer endpoints read it as positive. The two vetoes force both $mx$ and $my$ to be read by the outer endpoints.

In either case $m\in S_a\cap S_c$, which forces $a<c$. If there is a zero reading of $ac$, the first clause already gives $a<c$. This proves transitivity on the entire set of labels, including labels taken from different targets.

For an actual target, label each slot with its true graph bits at the designated readings. Every adjacent edge survives because a veto would certify a triangle in $G$. An absent adjacent edge fails its designated reading. At the outer pair, a comparison gives a zero reading of its graph bit. An incomparable outer pair has positive readings, and a common positive middle slot would certify a triangle in $G$. This gives an induced embedding by slot.

## Bound the number of labels

Suppose each pair outside $H$ has a default graph bit determined by the template. For a target, assume each slot disagrees with the defaults at at most $d$ pairs outside $H$.

Assign each edge of $H$ to one endpoint so that no slot reads more than $k=\lceil n/4\rceil$ such edges. For any nonempty set $W$ of slots, Mantel's theorem gives
$$
e(H[W])\le |W|^2/4\le k|W|.
$$
To apply Hall's theorem, give every slot $k$ copies and match every edge to one copy of either endpoint. A set of edges with endpoint set $W$ has at most $k|W|$ members and has $k|W|$ possible copies in its neighborhood. Fix one such assignment for the whole template.

Write the bits read on $H$ explicitly. Outside $H$, record only the set of at most $d$ deviations from the defaults. The two-endpoint decoder has access to a full reading outside $H$, since each endpoint reconstructs its read bits from the defaults and its own deviations. The host for one template consequently has at most
$$
n\,2^{\lceil n/4\rceil}\sum_{i=0}^{d}\binom{n}{i}
$$
vertices. Include all labels within this budget. The decoder proof permits arbitrary labels, even when two labels disagree about a bit stored at both endpoints.

## Obtain a bounded family of templates for each error tolerance

Fix $0<\delta<1/64$ and choose $0<\varepsilon<\delta/4$. Apply the equitable Szemerédi regularity lemma with a partition refining $A,M,C$ outside its exceptional class $V_0$. It gives $t\le T(\varepsilon)$ nonexceptional clusters of equal size $q$, at most $\varepsilon n$ exceptional vertices, and at most $\varepsilon t^2$ irregular cluster pairs.

Call a cross-rank cluster pair dense regular if it is regular and its graph density is at least $\delta$. The graph of dense regular pairs is triangle-free. If three clusters had three such pairs, a vertex of the first cluster could be chosen with at least $(\delta-\varepsilon)q$ neighbors in each of the other two. For each of the two pairs, regularity excludes fewer than $\varepsilon q$ vertices from that degree bound. The two neighbor sets are large enough to apply regularity to the third pair, and its density between those sets is positive. This gives a triangle in $G$, a contradiction.

The template graph $H$ consists of the complete bipartite graphs on the dense regular cluster pairs. Its rank slots outside the exceptional class are consecutive within each cluster. Its exceptional slots have no edges of $H$.

Count the positive cross-rank bits outside $H$ before promotion. Regular pairs below density $\delta$ contribute at most $\delta n^2$. Irregular pairs contribute at most $\varepsilon t^2q^2\le\varepsilon n^2$. Pairs incident to $V_0$ contribute at most $\varepsilon n^2$. Thus this graph of positive bits has at most $(\delta+2\varepsilon)n^2\le 2\delta n^2$ edges. At most $4\sqrt\delta\,n$ vertices have degree greater than $\sqrt\delta\,n$ in it.

Promote all those high-degree vertices, and $V_0$, to exceptional slots. Delete their incident edges from $H$ and add the promoted vertices back using the extension lemma below. With the exceptional vertices removed, the remaining $H$ is still triangle-free, and the residual graph of deviations has maximum degree at most $\sqrt\delta\,n$. Its defaults are all zero.

Use one fixed size for each cluster at a given $n,t$. Give all $t$ clusters $\lfloor n/t\rfloor$ slots, since $q\le\lfloor n/t\rfloor$, and leave the surplus and promoted slots vacant in the embedding. Read zero on all signed pairs involving a vacant slot. Equivalently, extend the signed core graph by isolated signed vertices. It stays triangle-free, and these extra slots contribute zero deviations. The Hall bound still uses at most $n$ slots.

A template is now specified by $t$, its cluster ranks, and the triangle-free graph of dense regular cluster pairs. For fixed $\varepsilon$, the number of templates is at most
$$
C_T=\sum_{t=1}^{T(\varepsilon)}3^t 2^{\binom t2},
$$
independently of $n$. Take their disjoint union as the core host $B$. With $d\le\lfloor\sqrt\delta\,n\rfloor$, its size is at most $C_Tn2^{\lceil n/4\rceil}\sum_{i=0}^d\binom ni$, and the binomial sum is at most $2^{h_2(\sqrt\delta)n}$, where $h_2$ is binary entropy.

### Add exceptional vertices while preserving the height bound

Let $B$ be the core host with three ordered ranks. Use a single pool of $k$ exception identifiers, sufficient for all targets under consideration. Attach to each base vertex disjoint sets $D,U\subseteq[k]$ recording the exceptions below and above it. For each identifier $i$, include an exceptional label at each of the three ranks for every pair $D,U$ with $D\cap U=\{i\}$. Its rank is part of the label. When embedding a target, treat $i$ as both below and above itself in its signature, and leave unused identifiers out of all signatures.

Between labels $x,y$ on strictly increasing ranks, declare $x<y$ if $D_x\subseteq D_y$, $U_y\subseteq U_x$, and either the base vertices compare in $B$ or $U_x\cap D_y\ne\varnothing$. The base comparison clause only applies to two base labels. In a chain, a witness on either step also witnesses the composite because the signatures nest. If neither step has a witness, both steps come from $B$ and so does the composite. This argument applies to all labels even when two labels using the same exception identifier carry different ranks. The strict rank condition bounds the height by three.

To embed a target, use its core embedding and the actual signatures and ranks. When a true comparison has an exceptional endpoint, that endpoint supplies the witness. A decoded comparison requires either a genuine core comparison or a genuine exceptional witness.

The base labels contribute $3^k|B|$ vertices. Exceptional labels contribute $3k3^{k-1}=k3^k$ for $k\ge1$. Choose $k=\lfloor(4\sqrt\delta+\varepsilon)n\rfloor$ uniformly over the targets. The combined bound is
$$
|U_n|\le 3^k\left(C_T n 2^{\lceil n/4\rceil}\sum_{i=0}^d\binom ni + k\right).
$$
In particular, for fixed $\delta,\varepsilon$ the logarithm of the size is at most
$$
\frac n4+\left[h_2(\sqrt\delta)+(4\sqrt\delta+\varepsilon)\log_2 3\right]n+\log_2 n+O_{\delta,\varepsilon}(1).
$$
Letting the fixed tolerance tend to zero yields the claimed $n/4+o(n)$ exponent. The host can be enumerated from templates and labels without listing target posets.

### A quantitative bound on the sublinear term

For a uniform explicit error, replace the equitable regularity step by the approximate homomorphism bound. Theorem 1.6 and (1.1) in [Fox and Zhao, Removal lemmas and approximate homomorphisms](https://arxiv.org/abs/2104.11626), with [Fox's triangle-removal bound](https://annals.math.princeton.edu/2011/174-1/p17), give the following statement. For $0<\eta<1/2$, every triangle-free $n$-vertex graph has a map to a triangle-free graph $F$ of order at most $T=\operatorname{tower}(O(\log(1/\eta)))$ that sends all but $\eta n^2$ edges to edges.

For the signed graph of a target, split each fiber of the map by the three target ranks. Use one slot per surviving vertex of a rank fiber. A pair is variable if its source ranks differ and its two fibers map to an edge of $F$. The variable graph is triangle-free. All other pairs have signed default zero. The graph of positive off-template bits has at most $\eta n^2$ edges. Promote every vertex of degree above $\sqrt\eta\,n$ in this graph to the exception set. There are at most $k=\lfloor 2\sqrt\eta\,n\rfloor$ such vertices, and the remaining deviations have maximum degree at most $d=\lfloor\sqrt\eta\,n\rfloor$. Use the exception lift with $k$ identifiers, omitting unused identifiers from the signatures.

There are at most $2^{\binom T2}(n+1)^{3T}$ choices of labelled $F$ and surviving rank fiber sizes. A smaller $F$ can be padded by isolated vertices. For each template use only its exact number of surviving slots. Mantel–Hall bounds its variable load by $\lceil n/4\rceil$. For a fixed original rank profile $(a_0,a_1,a_2)$, one can instead use $\lceil\max_i a_i(n-a_i)/n\rceil$, by the rank-profile bound below and monotonicity of $xy/(x+y)$ in both coordinates. Indeed the core rank size and its complement are both at most their original sizes. Use only template profiles consistent with these inequalities for the fixed-rank host.

The logarithmic costs of the deviation lists and exception lift sum to $O(n\sqrt\eta\log(1/\eta))$, by the binomial entropy bound and the $O(2^k)$ pooled lift. The template dictionary and slot names add $O(T^2+T\log(n+1)+\log(n+1))$. Let $L=\log_2^* n$ and take $\eta=2^{-aL}$ for a sufficiently small absolute constant $a>0$. The tower bounding $T$ has height at most $L/2$ for large $n$, so the dictionary and slot costs are $o(n2^{-aL/4})$. Also $n\sqrt\eta\log(1/\eta)=O(n2^{-aL/4})$. Thus for some absolute $c>0$ the full height-three host satisfies
$$
\log_2|U_n|\le \frac n4+O\!\left(n2^{-c\log_2^* n}\right).
$$
The same error bound above replaces the rank-profile $o(n)$ in the upper estimate. This decay comes from the tower height in the approximate homomorphism bound. A polynomial prefactor would require an additive $O(\log n)$ term in the logarithm of the host size.

## Lower bound and polynomial overhead

For the connected pure lower bound, use one bottom vertex and two nearly equal middle and top ranks. Make the bottom vertex less than every middle vertex. In the middle-to-top bipartite graph, choose one middle vertex adjacent to every top vertex and one top vertex adjacent to every middle vertex. Each of the remaining $(|M|-1)(|C|-1)$ bits is free. Every target is connected and pure. A host of size $N$ provides at most $N^n$ labeled placements, so $N\ge 2^{n/4-O(1)}$.

The decoder gives polynomial overhead whenever a polynomial-size family of templates suffices with $O(1)$ deviations per ordinary slot and $O(\log n)$ exceptional slots. The regularity step above yields an $o(n)$ overhead in the exponent. A template theorem at the stronger scales would make this a polynomial-factor construction.

### A reduction to nearly complete balanced cuts

Use a fixed tolerance in the regularity construction. For a variable template $H$ on $N\le n$ slots, let
$$
\beta(H)=\max_{\varnothing\ne W\subseteq V(H)}\frac{e(H[W])}{|W|},
\qquad
D=k+\log_2\left(\sum_{i=0}^d\binom ni\right),
$$
where $d$ is the uniform deviation cap and $k$ is the exception budget. Hall gives variable read load at most $\lceil\beta(H)\rceil$ by the definition of $\beta$. With the pooled exception lift below, all templates satisfying $\beta(H)+D\le n/4$ together contribute $O(n2^{n/4})$ vertices. The constant depends on the fixed tolerance through the template count. More generally, $\beta(H)+D\le n/4+c\log_2 n$ gives degree at most $1+c$ for these templates.

Every remaining template has a quantitative stability property. Mantel's theorem gives
$$
\frac{e(H[W])}{|W|}
\le \min\left(\frac{|W|}{4},\frac{e(H)}{|W|}\right)
\le\frac{\sqrt{e(H)}}2.
$$
Thus $\beta(H)+D>n/4$ and $D<n/4$ imply $e(H)>4(n/4-D)^2$. In particular its Mantel deficit $\Delta=N^2/4-e(H)$ is at most $2nD$.

Take a maximum-degree vertex, let $L$ be its neighborhood, and let $R=V(H)\setminus L$. Triangle-freeness makes $L$ independent. The degree sum on $R$ gives $e(H)+e(H[R])\le |L||R|$. Consequently there are at most $\Delta$ variable edges inside $R$, at most $2\Delta$ missing cross pairs, and $\big||L|-N/2\big|\le\sqrt{\Delta}$. For sufficiently small fixed tolerance, this reduces the polynomial-factor problem to targets represented near balanced, nearly complete bipartite variable templates. The conclusion concerns the variable template. Its cross pairs can still carry arbitrary target bits.

### The exponent as a function of the three rank sizes

For a triangle-free tripartite graph $H$ with rank sizes $s_0,s_1,s_2$ and $N$ total slots, one has
$$
e(H)\le\max_i s_i(N-s_i).
$$
Indeed, in each rank in turn replace the neighborhood of every vertex by that of a maximum-degree vertex of the rank. This creates no triangle because the rank is independent, and it preserves all previously made twin classes. The number of edges never decreases. The final graph is a blow-up of a triangle-free graph on three vertices, so its edges are incident to one rank. Empty ranks obey the same bound. Apply the bound to each induced subset $W$ and use the monotonicity of $xy/(x+y)$ to obtain
$$
\beta(H)\le \max_i\frac{s_i(N-s_i)}{N}.
$$

For a target with rank sizes $a_0,a_1,a_2$, the padded template is formed by removing at most $k$ target vertices and adding at most $k$ unused slots. For each $i$, the sizes of rank $i$ and of its complement in the template each differ from their input sizes by at most $k$. Since $xy/(x+y)$ is $1$-Lipschitz in each coordinate, this bounds $\beta(H)$ by
$$
\frac{\max_i a_i(n-a_i)}n+2k.
$$
As the fixed tolerance tends to zero, $2k+D=o(n)$ in the resulting asymptotic bound. The estimate is uniform over the rank profiles.

There is a matching exponent from counting. Fix the rank $i$ attaining the maximum and allow comparisons on pairs incident to that rank to vary. With all three ranks nonempty, fix a bottom point $a$ and a middle point $m$ to supply rank witnesses. If the varying rank is bottom, take $m$ below all top points and use no other middle-to-top edges. Prescribe $a$ below every middle and top point, and prescribe $a$ as the sole predecessor of $m$ on the bottom floor. If the varying rank is middle, prescribe all bottom–top comparisons, $a$ below every middle point, and $m$ below every top point. If the varying rank is top, let $a$ be the sole bottom predecessor of every middle point, and prescribe $a,m$ below every top point. In each case the remaining incident comparison bits vary freely and yield the required longest-chain ranks. At most $O(n)$ incident bits were prescribed. For height two, one fixed bottom point below all points of rank one supplies the witnesses. The antichain case gives the trivial exponent zero. Counting labelled placements into a host therefore yields the rank-profile bound
$$
\log_2 u(a_0,a_1,a_2)
=\frac{\max_i a_i(n-a_i)}{n}+o(n)
=\frac n4-\frac{\min_i(a_i-n/2)^2}{n}+o(n),
$$
where $u$ is the minimum host size for the prescribed rank profile.

In particular, fix $\gamma>0$ and consider all rank profiles with $\min_i|a_i-n/2|\ge\gamma n$. Choose a single fixed tolerance with $2k+D\le\gamma^2n/2$. The same constant template family then yields a host for that entire class with $O_\gamma(n2^{(1/4-\gamma^2/2)n})$ vertices. The general polynomial-factor question can therefore concentrate on the strip where some rank approaches half the target size.

### Width of the remaining rank strip

The quantitative error bound above also makes the rank reduction uniform in a shrinking strip. For some constants $K,c>0$, one host of size $O(2^{n/4})$ covers all targets with
$$
\min_i |a_i-n/2|\ge K n 2^{-c\log_2^* n/2}.
$$
Indeed, in the approximate-homomorphism construction use the exact surviving rank sizes. The read budget is at most the original rank-profile rate by monotonicity. Keep only templates with variable load low enough to absorb the common bound $O(n2^{-c\log_2^* n})$ for deviation, lift and dictionary costs. Every rank profile in the displayed class reaches such a template, since its load saves $\min_i(a_i-n/2)^2/n$. A single filtered union suffices, with the global dictionary counted once.

## Triangle-free graph hosts and the bipartite case

Let $G$ be a triangle-free graph, with no loops. Make three copies of its vertex set, one per rank. For adjacent ranks, decode a comparison exactly when the original vertices are adjacent in $G$. From bottom to top, decode a comparison exactly when they are nonadjacent in $G$. A chain across two adjacent pairs forces the outer comparison because $G$ has no triangle. If the two endpoints are copies of the same vertex, looplessness gives the outer comparison too. This is a height-at-most-three poset on $3|V(G)|$ vertices.

Every induced embedding of a target signed graph into $G$ lifts to an induced embedding of the target poset using its rank copies. The graph embedding can be chosen independently of the target rank sizes.

Conversely, a height-at-most-three poset universal for $n+4$ vertices yields a tripartite triangle-free graph universal for all triangle-free tripartite graphs on $n$ vertices. Give the input graph any proper three-coloring and decode it into a poset with ranks $A,M,C$. Add a bottom anchor $a_0$, a top anchor $c_0$, and two middle anchors $u,v$. Require $a<u<c_0$ for every $a\in A$, $a_0<m<c_0$ for every $m\in M$, and $a_0<v<c$ for every $c\in C$. Take transitive closure. These anchor paths preserve the induced original poset. Every original vertex now appears in its prescribed position on a three-element chain. In any embedding into a host of height at most three, longest-chain ranks therefore agree with the prescribed ranks. Take the signed graph of the host to obtain the claimed induced graph embedding. Thus the polynomial-factor question transfers in both directions, with at most four extra target vertices or three times as many host vertices.

There is an elementary Hall bound for the bipartite-signed family. For a fixed bipartition size $p+q=n$, assign each of the $pq$ possible edges to one endpoint at load at most $\lceil pq/n\rceil$. The vertices of a bipartite graph host are a slot and its owned bits. This gives a bipartite host of size $n2^{\lceil pq/n\rceil}$ for the split. The disjoint union over $p$, followed by the three-copy poset construction, uses $O(n^{3/2}2^{n/4})$ vertices. Indeed $pq/n=n/4-(p-n/2)^2/n$, and the sum of $2^{-(p-n/2)^2/n}$ over $p$ is $O(\sqrt n)$.

If the target signed graphs are bipartite, a degree-zero bound follows from [Alstrup, Kaplan, Thorup and Zwick, Theorem 8.3](https://arxiv.org/abs/1404.3391). Their distinct adjacency labels have length $n/4+O(1)$. Append one bit specifying the bipartition side. On the set of labels, permit decoded edges only between opposite sides. Genuine labelled embeddings are preserved, and the graph on all labels is bipartite. Applying the three-copy construction gives a single height-three host of size $O(2^{n/4})$ for all rank sizes simultaneously.

This size is sharp up to a constant for the bipartite-signed family. Balanced height-two targets already give $2^{\lfloor n^2/4\rfloor}$ labelled comparison patterns on the two parts, while an $N$-vertex host has at most $N^n$ placements. The full height-three family still has the general $2^{n/4+o(n)}$ bound above.

## Cut templates with fixed within-side graphs

Let a signed target on $N$ core positions have a cut of sizes $p,q$. Choose its within-side signed graphs as fixed defaults on their cross-rank pairs. Make every cross-cut, cross-rank pair variable. The variable graph $H$ is bipartite. The decoder works with any fixed defaults because each off-template pair is still read at both endpoints.

If a set of slots $W$ uses $u$ slots on the first side and $v$ on the second, then $e(H[W])\le uv$. For nonempty $W$ we have $uv/(u+v)\le pq/(p+q)$, by monotonicity in both coordinates. Hall therefore assigns the variable reads at load at most $\lceil pq/N\rceil$ per slot. With at most $d$ off-template deviations per slot, the total size for this template is at most
$$
N\,2^{\lceil pq/N\rceil}\sum_{i=0}^d\binom Ni.
$$
For all templates with a given pair of rank-colored within-side graphs up to isomorphism, use one canonical slot order on each side. Any target with those within-side graphs can align its slots by those isomorphisms. The bits across the cut then vary freely subject to the target being triangle-free.

When the within-side components have order bounded by a fixed $b$, they come from a finite set of connected rank-colored isomorphism types. The multiplicities of the types on each side specify the default pattern. There are polynomially many multiplicity vectors, and $d=0$, so the resulting host has size $N^{O_b(1)}2^{N/4}$. The exception lift also gives a polynomial factor for this class after deletion of $O(\log N)$ exceptional vertices.

An unbalanced cut offers slack for deviations:
$$
\frac N4-\frac{pq}{N}=\frac{(p-q)^2}{4N}.
$$
For example a $1:2$ split saves $N/36$ bits before rounding. For $d\le N/400$ the deviation cost is at most $h_2(1/400)N<0.02522N$, and this fits within the saving for large $N$. With polynomially many default patterns this gives a polynomial-factor bound even with these linear deviation budgets.

For nonuniform budgets, let $c_x$ be the number of bits allocated to slot $x$'s off-template deviations. A per-label budget $L$ is feasible for the variable reads exactly when
$$
e(H[W])+\sum_{x\in W}c_x \le L\,|W|
\qquad\text{for every }W\subseteq V(H).
$$
The singleton conditions make all capacities $L-c_x$ nonnegative. Apply Hall with $L-c_x$ copies of slot $x$. This lets slots with small deviation lists compensate for more expensive slots.

### Saving cross-cut bits from a fixed matching

Suppose $p,q>0$ and there is a matching of size $m$ within the side of size $p$. Put these matching edges in the fixed signed defaults and require them to remain present. For each vertex on the other side, its two cross bits to a matching edge have three possible patterns because a triangle is forbidden. Let $\zeta=2-\log_2 3$. We can reduce the cross-cut variable cost per label from $pq/(p+q)+O(1)$ to
$$
\frac{(p-\zeta m)q}{p+q-\zeta m}+O(1).
$$

To assign readings, group the left slots into $m$ pairs and $p-2m$ singletons. Set $w=p-\zeta m$ and $b=\lceil wq/(w+q)\rceil$. For each group, let its left slots read their bits to the same $b$ right slots. The other $q-b$ right slots read the whole group. Lay out the sets of right readers as consecutive cyclic intervals of length $q-b$, independently for the stream of pairs and the stream of singletons. Hence each right slot reads at most $\lceil m(q-b)/q\rceil$ pairs and $\lceil(p-2m)(q-b)/q\rceil$ singletons. The number of choices is bounded by $3$ per pair and $2$ per singleton, so the binary logarithm of the right label count is at most $w(q-b)/q+1+\log_2 3\le b+1+\log_2 3$. Each left slot reads at most $b$ ordinary bits. Dropping the same-rank pairs only decreases the costs. The resulting label sets are valid for the signed decoder, which is transitive for arbitrary labels obeying the designated readings.

For $p=q=N/2$ this saves at least $\zeta m/4$ bits (about $0.104m$) per slot before rounding. Any remaining deviations still use the same deviation lists. For instance, with $k=0$ and polynomially many default patterns, a balanced cut now suffices when $\log_2\sum_{i=0}^d\binom Ni$ is at most $\zeta m/4+O(\log N)$. This leaves a structural question for the nearly balanced templates in the reduction above: whether one can choose default patterns and residual lists so that the saved cross bits pay for their description.

The [matching and stability replay](../experiments/height-three-universal-posets/verify_matching_slack.py) checked 9,216 cyclic read layouts and all 1,699 triangle-free signed graphs with ranks $(2,2,2)$.

### Compact templates for bounded components on the two sides of a cut

The signed decoder also works when the single-reader variable graph contains triangles, provided the reader directions contain no directed triangle. Direct a variable pair from its reader to the other slot. Double-read pairs carry no direction in this test. Use a common-positive-slot veto on all slots, and put the rank on the label. Set the signed bit of a slot with itself to zero.

For transitivity, consider a two-step chain with middle slot $y$ and distinct outer slots $u,v$. If both outer labels use the same slot, the signed self bit is zero and the outer comparison holds. Otherwise, suppose every reading of $uv$ is positive and name a reader $u$. The comparison between $u$ and $y$ forces $y$ to have no positive reading of $yv$, and the comparison between $y$ and $v$ then implies that $yv$ is read only by $v$. If both ends read $uv$, the same argument forces $yu$ to be read by $u$. If only $u$ reads $uv$, there are directions $u\to v\to y$. A sole reader $y$ for $yu$ would finish a directed triangle. Thus $u$ reads $yu$ in either case. The comparisons make both outer labels read $y$ positively, which supplies the outer comparison. For a genuine signed target, every veto on a positive signed pair would give a triangle, so the encoded embedding is induced. In particular two different rank profiles can use the same slot template.

Suppose the signed graph admits a cut of sizes $p,q$ such that every connected component inside either side has at most $s$ vertices. Put $L=\operatorname{lcm}(1,\ldots,s)$. On a side of size $p$, prescribe $\max(0,\lfloor p/L\rfloor-(s-1))$ blocks of size $L$ and one remainder of size less than $sL$. This layout depends only on $p,s$. For each component size $j$, group $L/j$ components at a time into a full block. There is less than one block left over for each size, so at least the prescribed number of full blocks can be chosen. Put everything else in the remainder. Do the same on the other side.

Make all pairs within a block variable, with their reads directed by one linear order. Across the cut use all pairs and choose one common direction for each pair of blocks. Pairs between different blocks on the same side have signed default zero. There is no directed triangle: inside one block the directions follow a linear order, and a triangle using two blocks has the same direction for its two cross-cut pairs.

For the full blocks on the two sides, apply Hall on the complete bipartite graph of blocks. If there are $P,Q$ full blocks, a slot reads at most $L\lceil PQ/(P+Q)\rceil$ full-block cross bits when $P+Q>0$. This is at most $pq/(p+q)+L$, by monotonicity in the full-block side sizes. Have ordinary slots own all comparisons to the opposite remainder. Comparisons between remainders can all be read on one side. The resulting maximum number of reads is at most
$$
\frac{pq}{p+q}+O(sL).
$$
There are three rank choices per slot and one template for each split size. Summing the slot count over $p+q=n$ gives
$$
|U_{n,s}|\le 2^{O(sL)}\,O(n^{3/2}2^{n/4}),
$$
using $pq/n=n/4-(p-n/2)^2/n$. This count shares the template across all within-side component isomorphism types and all target rank profiles.

For $L(t)=\operatorname{lcm}(1,\ldots,t)$, the ratio $L(2t)/L(t)$ divides $\binom{2t}{t}$: any prime power in $(t,2t]$ supplies one factor of its prime to that binomial coefficient. Iterating at powers of two gives $L(s)\le 2^{4s}$. Thus $s\le\frac18\log_2\log_2 n$ still gives a bound of $n^{3/2+o(1)}2^{n/4}$ for this family.

The [reader direction and packing replay](../experiments/height-three-universal-posets/verify_directed_readers.py) checks all 512 assignments of labels to reader patterns on three slots, all 1,699 signed targets on ranks $(2,2,2)$, and 59,947 component-size profiles.

### A limitation of zero defaults

For integers $r,s$, take one bottom vertex $a_x$ per binary string $x\in\{0,1\}^r$. In each coordinate $i$, use a middle block $M_i$ and a top block $C_i$ of size $s$, with every signed edge between $M_i$ and $C_i$. Join $a_x$ in the signed graph to all of $M_i$ if $x_i=0$ and to all of $C_i$ if $x_i=1$. These are all the signed edges. There is no triangle because any triangle would require a string to have both bit values in the same coordinate.

Suppose a zero-default representation promotes at most $k$ vertices and omits at most $d$ positive signed edges per remaining slot from a triangle-free variable template. If $s>k+2d$, take two distinct surviving strings $x,y$ and a differing coordinate, ordered so $x_i=0$ and $y_i=1$. At least $s-k-d$ vertices of $M_i$ are joined to $a_x$ in the variable template, and at least $s-k-d$ vertices of $C_i$ are joined to $a_y$. Choose one surviving $m$ in the first set. The second set has more than $d$ vertices, so one of them, $c$, still has its variable edge to $m$. This gives a three-edge path $a_x,m,c,a_y$ in the variable template.

If the template is a blow-up of a triangle-free cluster graph, equal cluster types for $a_x$ and $a_y$ would turn this path into a triangle in the cluster graph. Thus at least $2^r-k$ clusters are needed. For $s=r^2$ this is almost the entire vertex set when $k=O(\log N)$ and $d=O(1)$, with $N=2^r+2rs$. The same family has one exact cut default pattern for each $r,s$: place the string vertices on one side and take the union of the fixed complete $M_i$–$C_i$ blocks on the other side.

A polynomial-factor bound for the full height-three family still requires a sufficiently small dictionary of default patterns, with residual costs that fit the Hall budget. Nearly balanced cuts are critical because the variable reads alone can reach $N/4$.

The [cut-default replay](../experiments/height-three-universal-posets/verify_cut_defaults.py) checks all 1,699 signed targets on ranks $(2,2,2)$ over all 32 cuts up to complementation. It verifies 54,368 induced embeddings and 66,303 two-step chains on arbitrary labels for selected defaults with one deviation allowed per slot.

## Sharing a rank across templates

For any family of height-three hosts with ranks $A_t,M_t,C_t$, keep the bottom and top ranks tagged by $t$ and use a common middle pool with $\max_t|M_t|$ slots. Map each $M_t$ injectively into that pool, keeping its adjacencies to its own outer ranks. Put every bottom vertex below every top vertex of a different tag. A two-step chain with endpoints of the same tag comes from the original host of that tag. Its middle vertex is the image of a unique middle vertex of that host. A chain with endpoints of different tags receives its outer comparison by construction. Each component embeds inducedly, since its outer vertices all have the same tag. The vertex count is
$$
\max_t|M_t|+\sum_t(|A_t|+|C_t|).
$$

There is a two-rank version. Suppose a common bipartite host contains an induced rank-preserving image of $A_t\cup M_t$ for each $t$. Share that bipartite host and retain separate top ranks. Attach a top vertex to its original image of $M_t$ and require its original comparisons to the image of $A_t$. Put all other bottom vertices below it. A two-step chain ending at this top vertex and starting within the image of $A_t$ comes from the original host because the image of $A_t\cup M_t$ is induced. Starting outside that image receives the new outer comparison. Thus the contribution of the first two ranks is just the size of the common bipartite host.

For the plain profile construction with ranks $(a,m,c)$, a middle profile has a nonempty lower mask and any upper mask. With $m$ copies per type its size is $m(2^a-1)2^c$, so over all rank profiles of total size $n$ the shared pool is at most $2^{n-1}$. For $s=a+c>0$, the outer part takes at most $s2^{\lceil ac/s\rceil}$ labels by Hall's theorem on the complete bipartite graph. Since $ac/s=s/4-(a-s/2)^2/s$, summing over $a$ contributes a factor $O(\sqrt{s})$ times $s2^{s/4}$. Summing over $s\le n$ gives $O(n^{3/2}2^{n/4})$ outer labels. This removes the factor of $n$ from the order of the vertex count of the plain construction. For Mantel–Hall templates the saving instead depends on the fraction of labels on the shared rank.

### Pooling exception profiles at cost $O(2^k)$

Let $B$ be a core host with $b_r$ vertices of rank $r$ for $r=0,1,2$. For one triple of exception counts $(k_0,k_1,k_2)$ summing to $k$, order the exception identifiers by rank. Use the signature decoder above. Every exception in a different rank from a label has one possible direction of comparison, determined by the ranks. Thus each contributes one bit. Exceptions in the label's own rank are incomparable apart from the mandatory self bit for an exceptional label. The number of labels on rank $r$ is at most
$$
(b_r+k_r)2^{k-k_r}.
$$
Every target with this exception profile embeds by ordering its exceptional vertices as prescribed.

Group the profiles by the rank $r$ of their smallest exception count, breaking ties by rank. Within such a group, pool the entire rank $r$ over all its profiles. If $r$ is middle, use the tagged outer comparisons described above. If it is bottom or top, retain the comparisons within each original profile and keep the other two ranks separate. In the latter case the two unpooled vertices of a two-step chain must come from the same profile, and the pooled endpoint must be in its image.

The pooled rank contributes at most $2^k\max_{j\ge0}(b_r+j)2^{-j}$. For an unpooled rank $i$ and a fixed value $k_i=j$, there are at most $j+1$ profiles in this group: $k_r$ can be any value from $0$ through $j$, and the remaining count is determined. Its total contribution is bounded by
$$
2^k\sum_{j\ge0}(j+1)(b_i+j)2^{-j}=O\!\left(2^k(b_i+1)\right).
$$
Sum over the three groups. This yields a height-three extension host of size $O(2^k(|B|+1))$ with an absolute constant, containing every height-three target whose core embeds into $B$ preserving its ranks. This replaces the earlier $3^k(|B|+k)$ bound. In the fixed-tolerance regularity estimate it replaces the factor $\log_2 3$ multiplying the exception count in the exponent by $1$, up to an additive constant.

Apply this when deleting at most $k$ vertices makes the signed graph bipartite. Choose exactly $k$ deletions, if necessary by moving additional vertices to the exception set. The signed core stays bipartite and keeps its original ranks. The degree-zero bipartite construction at size $n-k$ and the pooled lift give
$$
|U_{n,k}|=O\!\left(2^k\,2^{(n-k)/4}\right)
         =O\!\left(2^{n/4+3k/4}\right).
$$
Thus $k\le\alpha\log_2 n$ gives polynomial degree $3\alpha/4$, and bounded $k$ gives degree zero. A polynomial-factor bound for the full family still requires covering the signed graphs with larger deletion budgets.

The [pooled-exception replay](../experiments/height-three-universal-posets/verify_pooled_exceptions.py) checks all exception rank profiles through three extra vertices on a four-vertex core. It tests 4,345 induced extension embeddings, transitivity after pooling, and preservation of all 20 fixed-profile components.

## Fixed-profile benchmark on 16 vertices

The [rank $(4,8,4)$ benchmark](../experiments/height-three-universal-posets/profile-benchmark/README.md) covers every target with those longest-chain rank sizes. Its capacity table gives a host of 657 vertices, with 32 outer labels and 625 middle labels. The exact verifier passed without symmetry pruning after checking 63,912,422 repeated-demand states. A successful middle placement covers every compatible choice of the full outer relation, including skipping covers. The explicit decoder was also checked on all of the host's two-step chains and replayed on 1,000 targets.

For that same profile the fixed cut with the middle rank on one side gives a 1,024-vertex universal host. The smallest individually compatible cut component under the tested encoding had median size 496 across the sample. Of the 1,000 targets, 887 fit in a cut component smaller than 657. The best shared single cut template for the sample, and the best disjoint union of at most two cut templates under that encoding, both cost 1,024 vertices.

## Finite checks

The decoder was tested on rank profiles $(1,2,1)$, $(2,2,2)$, $(2,3,2)$, and $(1,2,4)$. For each profile, the test enumerated every triangle-free graph as a target and every triangle-free graph as a template. It used two endpoint assignments for each template, obtained by reversing the endpoint preference in the matching search. The checks covered 823,907,288 target-template-assignment combinations and 47,204,506 two-step paths on arbitrary decoder labels. These tests exercise the decoder independently of the regularity argument.

Run the [finite verifier](../experiments/height-three-universal-posets/check_decoder.cpp) from the repository root with a C++17 compiler.

```sh
work=$(mktemp -d)
c++ -O3 -std=c++17 -Wall -Wextra -pedantic \
  experiments/height-three-universal-posets/check_decoder.cpp -o "$work/check_decoder"
"$work/check_decoder"
```

## Lean source

The [Lean source](HeightThreeBound.lean) contains the counting lower bound, the decoder and extension lemmas, and the statement of the asymptotic upper bound. The asymptotic proof is written out in prose. The Lean snapshot awaits compiler verification.

## References

- Balogh, Garcia, and Sales, [Even smaller universal posets](https://arxiv.org/html/2607.12980v1), Theorem 3.1 for the refining regularity lemma and Section 5 for the three-layered question.
- Bonamy, Esperet, Groenland, and Scott, [Optimal labelling schemes for adjacency, comparability, and reachability](https://arxiv.org/abs/2012.01764), for the broader use of regularity in adjacency labeling.
