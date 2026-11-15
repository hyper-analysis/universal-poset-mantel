import Mathlib

/-!
# Induced-universal posets of height at most three

The declarations below give the target asymptotic statement, the counting lower
bound, the exact label count for one template, and the decoder, and the exceptional-slot extension. The proof of the asymptotic upper bound and the remaining
formalization steps are recorded at the end of the file.
-/

namespace HeightThree

open scoped BigOperators

/-- Strict order with a rank in three levels. The rank condition ensures
irreflexivity and excludes chains of length four. Every finite poset of height
at most three admits these ranks by taking longest chains ending at a vertex. -/
structure RankedOrder (α : Type) where
  rank : α → Fin 3
  rel : α → α → Prop
  rank_lt : ∀ {x y}, rel x y → rank x < rank y
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def Induced {α β : Type} (P : RankedOrder α) (Q : RankedOrder β)
    (f : α → β) : Prop :=
  Function.Injective f ∧ ∀ x y, P.rel x y ↔ Q.rel (f x) (f y)

/-- The host has to embed every order of the given size. Its own ranks may
differ from the input ranks under an embedding. -/
def Universal {β : Type} (n : ℕ) (Q : RankedOrder β) : Prop :=
  ∀ (α : Type) [Fintype α], Fintype.card α = n →
    ∀ P : RankedOrder α, ∃ f : α → β, Induced P Q f

/-- The intended asymptotic upper bound, stated by quantifying over the
allowance in the exponent. -/
def AsymptoticUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ N : ℕ, ∃ Q : RankedOrder (Fin N),
      Universal n Q ∧ (N : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ))

/-! ## Counting lower bound -/

/-- The (a b) bits between two levels can be chosen independently. -/
def bipartite {a b : ℕ} (bits : (Fin a × Fin b) → Bool) :
    RankedOrder (Sum (Fin a) (Fin b)) where
  rank := Sum.elim (fun _ => 0) (fun _ => 1)
  rel x y :=
    match x, y with
    | .inl i, .inr j => bits (i, j) = true
    | _, _ => False
  rank_lt := by
    intro x y h
    cases x <;> cases y <;> first | contradiction | decide
  trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> contradiction

theorem counting_lower_bound {a b : ℕ} {β : Type} [Fintype β]
    {Q : RankedOrder β} (hQ : Universal (a + b) Q) :
    2 ^ (a * b) ≤ (Fintype.card β) ^ (a + b) := by
  classical
  have embeds : ∀ bits : (Fin a × Fin b) → Bool,
      ∃ f : Sum (Fin a) (Fin b) → β, Induced (bipartite bits) Q f :=
    fun bits => hQ (Sum (Fin a) (Fin b)) (by simp) (bipartite bits)
  choose embedding hEmbedding using embeds
  have injectiveEmbedding : Function.Injective embedding := by
    intro lhs rhs h
    funext pair
    rcases pair with ⟨i, j⟩
    have hL := (hEmbedding lhs).2 (Sum.inl i) (Sum.inr j)
    have hR := (hEmbedding rhs).2 (Sum.inl i) (Sum.inr j)
    rw [h] at hL
    have hBits : lhs (i, j) = true ↔ rhs (i, j) = true := hL.trans hR.symm
    cases h₁ : lhs (i, j) <;> cases h₂ : rhs (i, j) <;>
      simp_all
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective _ injectiveEmbedding

theorem lower_bound {n : ℕ} {β : Type} [Fintype β]
    {Q : RankedOrder β} (hn : 0 < n) (hQ : Universal n Q) :
    2 ^ (n / 4) ≤ Fintype.card β := by
  let q := n / 4
  let a := 2 * q
  let b := n - a
  have hab : a + b = n := by
    dsimp [a, b, q]
    omega
  have hnb : n ≤ 2 * b := by
    dsimp [b, a, q]
    omega
  have hprod : q * n ≤ a * b := by
    calc
      q * n ≤ q * (2 * b) := Nat.mul_le_mul_left _ hnb
      _ = a * b := by
        dsimp [a]
        ring
  have hcount := counting_lower_bound (a := a) (b := b) (Q := Q)
    (by simpa only [hab] using hQ)
  rw [hab] at hcount
  have hpower : (2 ^ q) ^ n ≤ (Fintype.card β) ^ n := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hprod).trans hcount
  by_contra! h
  have hstrict : Fintype.card β ^ n < (2 ^ q) ^ n :=
    Nat.pow_lt_pow_left h (by omega)
  exact (not_lt_of_ge hpower) hstrict

/-! ## Decoder transitivity for arbitrary stored bits -/

/-- Which of the two endpoints reads a pair. Outside a template both read it.
Inside the template exactly one endpoint reads it. -/
structure Readers where
  left : Prop
  right : Prop
  covers : left ∨ right

def Readers.single (r : Readers) : Prop := ¬ (r.left ∧ r.right)

def Readers.allPositive (r : Readers) (p q : Prop) : Prop :=
  (r.left → p) ∧ (r.right → q)

def leftPositive (r : Readers) (p : Prop) : Prop := r.left ∧ p
def rightPositive (r : Readers) (q : Prop) : Prop := r.right ∧ q

/-- These are the three slots occupied by a potential chain. The six stored
bits are arbitrary. Vetoes on other slots can only rule out an adjacent step,
so it suffices to use each adjacent step's veto at the third slot. -/
theorem decoder_triangle
    (am mc ac : Readers)
    (noTriangle : ¬ (am.single ∧ mc.single ∧ ac.single))
    (a_m m_a m_c c_m a_c c_a : Prop)
    (adjAM : am.allPositive a_m m_a)
    (adjMC : mc.allPositive m_c c_m)
    (vetoAM : ¬ (leftPositive ac a_c ∧ leftPositive mc m_c))
    (vetoMC : ¬ (rightPositive am m_a ∧ rightPositive ac c_a)) :
    ¬ ac.allPositive a_c c_a ∨
      (leftPositive am a_m ∧ rightPositive mc c_m) := by
  classical
  have amCovers := am.covers
  have mcCovers := mc.covers
  have acCovers := ac.covers
  unfold Readers.single at noTriangle
  unfold Readers.allPositive at *
  unfold leftPositive rightPositive at *
  tauto

/-- A label's rank, slot, and its positive readings on designated pairs. -/
structure Label (Slot : Type) where
  slot : Slot
  positive : Slot → Prop

def comparesUp {Slot : Type} (rank : Slot → Fin 3)
    (reading : Slot → Slot → Readers) (x y : Label Slot) : Prop :=
  let r := reading x.slot y.slot
  let accept := r.allPositive (x.positive y.slot) (y.positive x.slot)
  let rankX := rank x.slot
  let rankY := rank y.slot
  rankX < rankY ∧
    if rankX = 0 ∧ rankY = 2 then
      ¬ accept ∨ ∃ m : Slot, rank m = 1 ∧
        leftPositive (reading x.slot m) (x.positive m) ∧
        rightPositive (reading m y.slot) (y.positive m)
    else
      accept ∧
        if rankX = 0 then
          ¬ ∃ c : Slot, rank c = 2 ∧
            leftPositive (reading x.slot c) (x.positive c) ∧
            leftPositive (reading y.slot c) (y.positive c)
        else
          ¬ ∃ a : Slot, rank a = 0 ∧
            rightPositive (reading a x.slot) (x.positive a) ∧
            rightPositive (reading a y.slot) (y.positive a)

theorem decoder_transitive {Slot : Type} (rank : Slot → Fin 3)
    (reading : Slot → Slot → Readers)
    (triangleFree : ∀ a m c : Slot, rank a = 0 → rank m = 1 → rank c = 2 →
      ¬ ((reading a m).single ∧ (reading m c).single ∧ (reading a c).single))
    {a m c : Label Slot}
    (ham : comparesUp rank reading a m) (hmc : comparesUp rank reading m c) :
    comparesUp rank reading a c := by
  classical
  have h₁ : rank a.slot < rank m.slot := ham.1
  have h₂ : rank m.slot < rank c.slot := hmc.1
  have ha : rank a.slot = 0 := by
    apply Fin.ext
    omega
  have hm : rank m.slot = 1 := by
    apply Fin.ext
    omega
  have hc : rank c.slot = 2 := by
    apply Fin.ext
    omega
  have ha₀ := ham.2
  have hm₀ := hmc.2
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  simp only [ha, hm, h12, eq_self, and_false, if_false, true_and, if_true] at ha₀
  simp only [hm, hc, h10, false_and, if_false] at hm₀
  refine ⟨h₁.trans h₂, ?_⟩
  simp only [ha, hc, eq_self, and_self, if_true]
  obtain hzero | ⟨hamLeft, hmcRight⟩ :=
    decoder_triangle _ _ _ (triangleFree _ _ _ ha hm hc)
      _ _ _ _ _ _ ha₀.1 hm₀.1
      (fun h => ha₀.2 ⟨c.slot, hc, h.1, h.2⟩)
      (fun h => hm₀.2 ⟨a.slot, ha, h.1, h.2⟩)
  · exact Or.inl hzero
  · exact Or.inr ⟨m.slot, hm, hamLeft, hmcRight⟩

/-! ## Genuine labels recover the input relation -/

def graphBit {Slot : Type} (P : RankedOrder Slot) (x y : Slot) : Prop :=
  if P.rank x = 0 ∧ P.rank y = 2 then ¬ P.rel x y else P.rel x y

private theorem no_input_triangle {Slot : Type} (P : RankedOrder Slot)
    {a m c : Slot} (ha : P.rank a = 0) (hm : P.rank m = 1) (hc : P.rank c = 2) :
    ¬ (graphBit P a m ∧ graphBit P m c ∧ graphBit P a c) := by
  rintro ⟨ham, hmc, hac⟩
  have ham' : P.rel a m := by simpa [graphBit, ha, hm] using ham
  have hmc' : P.rel m c := by simpa [graphBit, hm, hc] using hmc
  have hac' : ¬ P.rel a c := by simpa [graphBit, ha, hc] using hac
  exact hac' (P.trans ham' hmc')

/-- The direction of a read is determined by the order of the two ranks. -/
def encode {Slot : Type} (P : RankedOrder Slot) (x : Slot) : Label Slot :=
  ⟨x, fun y => if P.rank x < P.rank y then graphBit P x y else graphBit P y x⟩

theorem decode_encode {Slot : Type} (P : RankedOrder Slot)
    (reading : Slot → Slot → Readers) (x y : Slot) :
    comparesUp P.rank reading (encode P x) (encode P y) ↔ P.rel x y := by
  classical
  have lt01 : (0 : Fin 3) < 1 := by decide
  have lt02 : (0 : Fin 3) < 2 := by decide
  have lt12 : (1 : Fin 3) < 2 := by decide
  have notLt10 : ¬ (1 : Fin 3) < 0 := by decide
  have notLt20 : ¬ (2 : Fin 3) < 0 := by decide
  have notLt21 : ¬ (2 : Fin 3) < 1 := by decide
  by_cases hxy : P.rank x < P.rank y
  · have hyx : ¬ P.rank y < P.rank x := not_lt_of_ge (le_of_lt hxy)
    have reads : (reading x y).allPositive (graphBit P x y) (graphBit P x y)
        ↔ graphBit P x y := by
      constructor
      · intro h
        exact (reading x y).covers.elim h.1 h.2
      · intro h
        exact ⟨fun _ => h, fun _ => h⟩
    simp only [comparesUp, encode, hxy, hyx, if_true, if_false, true_and, reads]
    by_cases hx : P.rank x = 0
    · by_cases hy : P.rank y = 2
      · have noExtra : (∃ m : Slot, P.rank m = 1 ∧
              leftPositive (reading x m)
                (if P.rank x < P.rank m then graphBit P x m else graphBit P m x) ∧
              rightPositive (reading m y)
                (if P.rank y < P.rank m then graphBit P y m else graphBit P m y)) →
            P.rel x y := by
          rintro ⟨m, hm, hxm, hmy⟩
          have hxm' : graphBit P x m := by
            simpa [hx, hm, lt01] using hxm.2
          have hmy' : graphBit P m y := by
            simpa [hy, hm, notLt21] using hmy.2
          by_contra h
          exact no_input_triangle P hx hm hy ⟨hxm', hmy', by simpa [graphBit, hx, hy]⟩
        simp only [hx, hy, eq_self, and_self, if_true]
        rw [show graphBit P x y ↔ ¬ P.rel x y by simp [graphBit, hx, hy]]
        constructor
        · exact fun h => h.elim (fun h' => Classical.byContradiction h') noExtra
        · exact fun h => Or.inl (fun hn => hn h)
      · have hy' : P.rank y = 1 := by
          apply Fin.ext
          omega
        have noVeto (h : P.rel x y) :
            ¬ ∃ c : Slot, P.rank c = 2 ∧
              leftPositive (reading x c)
                (if P.rank x < P.rank c then graphBit P x c else graphBit P c x) ∧
              leftPositive (reading y c)
                (if P.rank y < P.rank c then graphBit P y c else graphBit P c y) := by
          rintro ⟨c, hc, hxc, hyc⟩
          exact no_input_triangle P hx hy' hc
            ⟨by simpa [graphBit, hx, hy'] using h,
              by simpa [hy', hc, lt12] using hyc.2,
              by simpa [hx, hc, lt02] using hxc.2⟩
        simp only [hx, hy, eq_self, true_and, if_false, if_true]
        rw [show graphBit P x y ↔ P.rel x y by simp [graphBit, hx, hy]]
        exact ⟨And.left, fun h => ⟨h, noVeto h⟩⟩
    · have hx' : P.rank x = 1 := by
        apply Fin.ext
        omega
      have hy' : P.rank y = 2 := by
        apply Fin.ext
        omega
      have noVeto (h : P.rel x y) :
          ¬ ∃ a : Slot, P.rank a = 0 ∧
            rightPositive (reading a x)
              (if P.rank x < P.rank a then graphBit P x a else graphBit P a x) ∧
            rightPositive (reading a y)
              (if P.rank y < P.rank a then graphBit P y a else graphBit P a y) := by
        rintro ⟨a, ha, hax, hay⟩
        exact no_input_triangle P ha hx' hy'
          ⟨by simpa [hx', ha, notLt10] using hax.2,
            by simpa [graphBit, hx', hy'] using h,
            by simpa [hy', ha, notLt20] using hay.2⟩
      simp only [hx, false_and, if_false]
      rw [show graphBit P x y ↔ P.rel x y by simp [graphBit, hx]]
      exact ⟨And.left, fun h => ⟨h, noVeto h⟩⟩
  · exact ⟨fun h => (hxy h.1).elim, fun h => (hxy (P.rank_lt h)).elim⟩

/-! ## Restore exceptional slots -/

structure Signature (α Ex : Type) where
  base : Option α
  rank : Fin 3
  below : Set Ex
  above : Set Ex

def extensionRel {α Ex : Type} (P : RankedOrder α) (x y : Signature α Ex) : Prop :=
  x.rank < y.rank ∧ x.below ⊆ y.below ∧ y.above ⊆ x.above ∧
    ((∃ a b, x.base = some a ∧ y.base = some b ∧ P.rel a b) ∨
      ∃ i, i ∈ x.above ∧ i ∈ y.below)

theorem extension_transitive {α Ex : Type} (P : RankedOrder α)
    {x y z : Signature α Ex} (hxy : extensionRel P x y) (hyz : extensionRel P y z) :
    extensionRel P x z := by
  rcases hxy with ⟨hxyRank, hxyBelow, hxyAbove, hxySource⟩
  rcases hyz with ⟨hyzRank, hyzBelow, hyzAbove, hyzSource⟩
  refine ⟨hxyRank.trans hyzRank, ?_, ?_, ?_⟩
  · intro i hi
    exact hyzBelow (hxyBelow hi)
  · intro i hi
    exact hxyAbove (hyzAbove hi)
  · rcases hxySource with ⟨a, b, ha, hb, hab⟩ | ⟨i, hix, hiy⟩
    · rcases hyzSource with ⟨b', c, hb', hc, hbc⟩ | ⟨i, hiy, hiz⟩
      · have heq : b = b' := Option.some.inj (hb.symm.trans hb')
        subst b'
        exact Or.inl ⟨a, c, ha, hc, P.trans hab hbc⟩
      · exact Or.inr ⟨i, hxyAbove hiy, hiz⟩
    · exact Or.inr ⟨i, hix, hyzBelow hiy⟩

/-! ## Counting labels for one template -/

abbrev Deviations (n d : ℕ) :=
  Σ i : Fin (d + 1), ↥((Finset.univ : Finset (Fin n)).powersetCard i.val)

/-- Pad the explicit reads to k bits. The second component is a set of at
most d slots, represented by its size and then the set of that size. -/
abbrev TemplateLabels (n k d : ℕ) := Fin n × (Fin k → Bool) × Deviations n d

theorem template_label_count (n k d : ℕ) :
    Fintype.card (TemplateLabels n k d) =
      n * 2 ^ k * ∑ i ∈ Finset.range (d + 1), n.choose i := by
  classical
  simp [TemplateLabels, Deviations, Fintype.card_fun, Fintype.card_sigma,
    Fin.sum_univ_eq_sum_range, Nat.mul_assoc]

/-! ## Take the union over a finite family of templates -/

/-- Comparisons are confined to one component of the disjoint union. -/
def disjointUnion {ι τ : Type} (components : ι → RankedOrder τ) :
    RankedOrder (ι × τ) where
  rank x := (components x.1).rank x.2
  rel x y := x.1 = y.1 ∧ (components x.1).rel x.2 y.2
  rank_lt := by
    intro x y h
    change (components x.1).rank x.2 < (components y.1).rank y.2
    rw [← h.1]
    exact (components x.1).rank_lt h.2
  trans := by
    intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, (components x.1).trans hxy.2 ?_⟩
    rw [hxy.1]
    exact hyz.2

theorem template_family_upper_bound {ι : Type} [Fintype ι]
    {n m k d : ℕ} (components : ι → RankedOrder (TemplateLabels m k d))
    (covers : ∀ (α : Type) [Fintype α], Fintype.card α = n →
      ∀ P : RankedOrder α, ∃ i : ι, ∃ f : α → TemplateLabels m k d,
        Induced P (components i) f) :
    Universal n (disjointUnion components) ∧
      Fintype.card (ι × TemplateLabels m k d) =
        Fintype.card ι * (m * 2 ^ k * ∑ j ∈ Finset.range (d + 1), m.choose j) := by
  constructor
  · intro α fin hcard P
    obtain ⟨i, f, hf⟩ := covers α hcard P
    refine ⟨fun x => (i, f x), ?_, ?_⟩
    · intro x y h
      exact hf.1 (congrArg Prod.snd h)
    · intro x y
      change P.rel x y ↔ (i = i ∧ (components i).rel (f x) (f y))
      simpa using hf.2 x y
  · rw [Fintype.card_prod, template_label_count]

/-!
## Proof of the asymptotic upper bound in ordinary mathematics

1. Rank an input poset by longest chains. Encode adjacent comparisons and
   bottom–top incomparabilities as graph edges. The graph is triangle-free.
   On genuine input labels, an adjacent veto or an outer common witness
   for an incomparable pair would give a triangle in this graph. Thus
   the decoder recovers the input relation in both directions.

2. Fix a small constant e > 0 and apply the equitable regularity lemma,
   with at least ceil(4/e) clusters, to the triangle-free encoding. Join
   two clusters in a reduced graph when their pair is e/8-regular and
   its density is at least e/4. The reduced graph is triangle-free by
   the triangle counting lemma. The actual input edges inside its joined
   cluster pairs leave fewer than e n^2 uncovered edges, by
   Mathlib's SimpleGraph.regularityReduced_edges_card_aux. This uses
   regularity on the graph before splitting clusters by rank.

3. In the graph of uncovered input edges, delete the vertices of degree
   greater than sqrt(e) n. There are at most 2 sqrt(e) n of them, by summing
   degrees. On survivors, split each cluster by each of the three ranks.
   Complete the joined cluster pairs across distinct ranks to get the
   triangle-free template H. The number of such templates up to relabeling
   is polynomial in n for fixed e: record the reduced cluster graph and
   the three surviving rank counts per cluster. Every uncovered bit at a
   surviving slot is a deviation from zero; there are at most sqrt(e) n.

4. Give each edge of H to one of its endpoints. Each slot can be charged
   at most ceil(n/4) times: any set of edges with endpoint set W has at
   most |W|^2/4 edges by Mantel and hence at most ceil(n/4)|W| edges.
   Hall's theorem applied to ceil(n/4) copies of each slot gives the
   assignment. Each edge outside H is read at both endpoints. The count
   in template_label_count gives at most
     n * 2^ceil(n/4) * 2^(h₂(sqrt(e)) n)
   labels per template, where h₂ is binary entropy. For 0 < ρ < 1/2,
   set t = ρ/(1−ρ). Since t^i ≥ t^(ρ n) for i ≤ ρ n, the binomial tail
   is bounded by t^(−ρ n)(1+t)^n = 2^(h₂(ρ)n). Take ρ = sqrt(e).
   decoder_transitive applies even to arbitrary mixtures of labels.

5. For k deleted vertices, make one copy for each assignment of their
   ranks. In it, decorate each surviving label with the sets D and U of
   deleted slots below and above it; they are disjoint. Also add labels
   at each deleted slot i, whose D and U meet exactly at i. For labels
   x and y on increasing ranks require D_x ⊆ D_y and U_y ⊆ U_x. Also
   require either a comparison between their surviving base labels or
   an index in U_x ∩ D_y. Along a two-step path, a witness index from
   either step survives the nested signatures; when both comparisons
   come from the base, use base transitivity. On genuine input labels
   these tests preserve and reflect comparisons, including comparisons
   incident to a deleted vertex, which witnesses itself. The cost is
   at most 9^k (|B| + k), for B the surviving host.

6. Take the disjoint union over templates and numbers of deleted slots.
   For fixed e, the logarithm of its size is at most
     n/4 + (h₂(sqrt(e)) + 2 sqrt(e) log₂ 9) n + O_e(log n).
   First pick e so that the coefficient in parentheses is less than
   half the requested allowance. Then take n large enough to absorb
   O_e(log n). This proves AsymptoticUpperBound.

The formal declarations above do not invoke steps 1–6 as axioms.
To derive AsymptoticUpperBound inside Lean, the reduction, bounded label encoding, exceptional-slot
embedding and count, and the analytic estimates must still be
connected to the existing Mathlib theorems. The Lean source was
reviewed without running a Lean compiler.
-/

end HeightThree
