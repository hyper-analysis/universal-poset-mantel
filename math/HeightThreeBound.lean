import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Induced-universal posets of height at most three

The Mantel–Hall construction proves `asymptotic_upper_bound` for all
height-at-most-three orders. The theorems `lower_bound` and
`connected_pure_lower_bound` give matching leading exponents for the full
family and for connected pure height-three targets.
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
    cases x <;> cases y <;> first | contradiction | (change (0 : Fin 3) < 1; decide)
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
  by_cases outer : ac.allPositive a_c c_a
  · right
    have noMiddleLeft (h : ac.right) : ¬ am.right := fun reader =>
      vetoMC ⟨⟨reader, adjAM.2 reader⟩, ⟨h, outer.2 h⟩⟩
    have noMiddleRight (h : ac.left) : ¬ mc.left := fun reader =>
      vetoAM ⟨⟨h, outer.1 h⟩, ⟨reader, adjMC.1 reader⟩⟩
    have leftReads : am.left := by
      by_contra missing
      have middleReads := am.covers.resolve_left missing
      have outerRight : ¬ ac.right := fun h => noMiddleLeft h middleReads
      have outerLeft := ac.covers.resolve_right outerRight
      exact noTriangle ⟨fun h => missing h.1,
        fun h => noMiddleRight outerLeft h.1, fun h => outerRight h.2⟩
    have rightReads : mc.right := by
      by_contra missing
      have middleReads := mc.covers.resolve_right missing
      have outerLeft : ¬ ac.left := fun h => noMiddleRight h middleReads
      have outerRight := ac.covers.resolve_left outerLeft
      exact noTriangle ⟨fun h => noMiddleLeft outerRight h.2,
        fun h => missing h.2, fun h => outerLeft h.1⟩
    exact ⟨⟨leftReads, adjAM.1 leftReads⟩, ⟨rightReads, adjMC.2 rightReads⟩⟩
  · exact Or.inl outer

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
  simp only [ha, hm, h12, eq_self, and_false, if_false, if_true] at ha₀
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
        · exact fun h => h.elim (fun h' => Classical.byContradiction h') (by simpa only [hx, hy] using noExtra)
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
        exact ⟨And.left, fun h => ⟨h, by simpa only [hx] using noVeto h⟩⟩
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
  simp [TemplateLabels, Deviations, Fintype.card_sigma,
    Fin.sum_univ_eq_sum_range, Nat.mul_assoc]

/-! ## Take the union over a finite family of templates -/

/-- Comparisons are confined to one component of the disjoint union. -/
def disjointUnion {ι τ : Type} (components : ι → RankedOrder τ) :
    RankedOrder (ι × τ) where
  rank x := (components x.1).rank x.2
  rel x y := x.1 = y.1 ∧ (components x.1).rel x.2 y.2
  rank_lt := by
    intro x y h
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


/-! ## The signed comparison graph and the Mantel–Hall allocation -/

open Finset Fintype SimpleGraph
open scoped Finset

/-- Adjacent comparisons and outer incomparabilities, with no edges within ranks. -/
def signedGraph {α : Type} (P : RankedOrder α) : SimpleGraph α where
  Adj x y := (P.rank x < P.rank y ∧ graphBit P x y) ∨
    (P.rank y < P.rank x ∧ graphBit P y x)
  symm := fun _ _ h => h.symm
  loopless := ⟨by simp⟩

private theorem triangle_of_adj {α : Type} [DecidableEq α] (G : SimpleGraph α) {x y z : α}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.IsNClique 3 {x, y, z} :=
  is3Clique_iff.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩

theorem signedGraph_cliqueFree {α : Type} (P : RankedOrder α) :
    (signedGraph P).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.1 hs
  suffices aux : ∀ a m c : α, P.rank a < P.rank m → P.rank m < P.rank c →
      (signedGraph P).Adj a m → (signedGraph P).Adj m c → (signedGraph P).Adj a c →
      False by
    have exy := hxy
    have exz := hxz
    have eyz := hyz
    rcases exy with ⟨h, _⟩ | ⟨h, _⟩
    · rcases exz with ⟨i, _⟩ | ⟨i, _⟩
      · rcases eyz with ⟨j, _⟩ | ⟨j, _⟩
        · exact aux x y z h j hxy hyz hxz
        · exact aux x z y i j hxz hyz.symm hxy
      · exact aux z x y i h hxz.symm hxy hyz.symm
    · rcases eyz with ⟨j, _⟩ | ⟨j, _⟩
      · rcases exz with ⟨i, _⟩ | ⟨i, _⟩
        · exact aux y x z h i hxy.symm hxz hyz
        · exact aux y z x j i hyz hxz.symm hxy.symm
      · exact aux z y x j h hyz.symm hxy.symm hxz.symm
  intro a m c ham hmc am mc ac
  have ha : P.rank a = 0 := Fin.ext (by omega)
  have hm : P.rank m = 1 := Fin.ext (by omega)
  have hc : P.rank c = 2 := Fin.ext (by omega)
  have edge {a b : α} (h : P.rank a < P.rank b) (e : (signedGraph P).Adj a b) :
      graphBit P a b := e.elim And.right (fun e => (h.asymm e.1).elim)
  exact no_input_triangle P ha hm hc ⟨edge ham am, edge hmc mc, edge (ham.trans hmc) ac⟩

private theorem mantel {α : Type} [Fintype α] (H : SimpleGraph α)
    [DecidableRel H.Adj] (hh : H.CliqueFree 3) :
    4 * #H.edgeFinset ≤ Fintype.card α ^ 2 := by
  have h := hh.card_edgeFinset_le (r := 2)
  have hr : Fintype.card α % 2 = 0 ∨ Fintype.card α % 2 = 1 := by omega
  rcases hr with hr | hr <;> simp [hr] at h <;> omega

/-- Each edge is assigned to one endpoint and one of its available bit positions. -/
structure Allocation {α : Type} (H : SimpleGraph α) (k : ℕ) where
  place : H.edgeSet ↪ α × Fin k
  endpoint : ∀ e, (place e).1 ∈ e.val

theorem allocation_exists {α : Type} [Fintype α] (H : SimpleGraph α)
    (hh : H.CliqueFree 3) {k : ℕ} (hk : Fintype.card α ≤ 4 * k) :
    Nonempty (Allocation H k) := by
  classical
  let options (e : H.edgeSet) : Finset (α × Fin k) := e.val.toFinset ×ˢ univ
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective options).1 (by
    intro edges
    let W := edges.biUnion fun e => e.val.toFinset
    let H' := H.induce (W : Set α)
    have hcard : #edges ≤ #H'.edgeFinset := by
      rw [← card_map (f := (Function.Embedding.subtype (· ∈ (W : Set α))).sym2Map)]
      apply card_le_card_of_injOn (fun e => e.val)
      · intro e he
        have hm (v : α) (hv : v ∈ e.val) : v ∈ W :=
          mem_biUnion.2 ⟨e, he, Sym2.mem_toFinset.2 hv⟩
        rcases e with ⟨e, heH⟩
        revert hm heH
        refine Sym2.inductionOn e ?_
        intro x y heH _ hm
        let a : (W : Set α) := ⟨x, hm x (by simp)⟩
        let b : (W : Set α) := ⟨y, hm y (by simp)⟩
        exact mem_map.2 ⟨s(a, b), mem_edgeFinset.2 ((H'.mem_edgeSet).2 (H.mem_edgeSet.1 heH)), rfl⟩
      · exact fun _ _ _ _ he => Subtype.ext he
    have hh' : H'.CliqueFree 3 := by
      exact hh.comap ⟨(SimpleGraph.Embedding.induce (G := H) (W : Set α)).toCopy⟩
    have hW : #W ≤ 4 * k := (card_le_univ W).trans (by simpa using hk)
    have hM : 4 * #H'.edgeFinset ≤ #W * #W := by
      simpa [H', pow_two] using mantel H' hh'
    have hmul := Nat.mul_le_mul_left #W hW
    have hbound : #edges ≤ #W * k := by
      rw [Nat.mul_left_comm] at hmul
      omega
    have hprod : edges.biUnion options = W ×ˢ (univ : Finset (Fin k)) := by
      ext ⟨x, i⟩
      simp [W, options, mem_biUnion, mem_product]
    simpa [hprod, card_product] using hbound)
  exact ⟨⟨⟨f, hf⟩, fun e => Sym2.mem_toFinset.1 (mem_product.1 (hmem e)).1⟩⟩

/-! ## A bounded reduced graph with few uncovered edges -/

private theorem no_triangle {α : Type} (G : SimpleGraph α) (hG : G.CliqueFree 3)
    {x y z : α} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  classical
  exact hG _ (triangle_of_adj G hxy hxz hyz)

private theorem cliqueFree_of_no_triangle {α : Type} (G : SimpleGraph α)
    (h : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z → False) : G.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := is3Clique_iff.1 hs
  exact h x y z hxy hxz hyz

private def clusterGraph {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (P : Finpartition (univ : Finset α))
    (e : ℝ) : SimpleGraph P.parts where
  Adj s t := s ≠ t ∧ G.IsUniform (e / 8) s.val t.val ∧ e / 4 ≤ G.edgeDensity s.val t.val
  symm s t := fun ⟨hne, hu, hd⟩ =>
    ⟨hne.symm, hu.symm, by rwa [edgeDensity_comm]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem clusterGraph_cliqueFree {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (P : Finpartition (univ : Finset α)) {e : ℝ} (he : 0 < e) (he₁ : e ≤ 1) :
    (clusterGraph G P e).CliqueFree 3 := by
  apply cliqueFree_of_no_triangle
  intro s t u hst hsu htu
  have disj {a b : P.parts} (h : a ≠ b) : Disjoint a.val b.val :=
    P.disjoint a.property b.property (fun heq => h (Subtype.ext heq))
  have hd (a : P.parts) : 0 < (#a.val : ℝ) :=
    Nat.cast_pos.mpr (P.nonempty_of_mem_parts a.property).card_pos
  have hst' : 2 * (e / 8) ≤ G.edgeDensity s.val t.val := by linarith [hst.2.2]
  have hsu' : 2 * (e / 8) ≤ G.edgeDensity s.val u.val := by linarith [hsu.2.2]
  have htu' : 2 * (e / 8) ≤ G.edgeDensity t.val u.val := by linarith [htu.2.2]
  have h := G.triangle_counting hst' hst.2.1 (disj hst.1)
    hsu' hsu.2.1 (disj hsu.1) htu' htu.2.1 (disj htu.1)
  rw [hG.cliqueFinset] at h
  simp only [Finset.card_empty, Nat.cast_zero] at h
  have hfirst : 0 < 1 - 2 * (e / 8) := by linarith
  exact (not_lt_of_ge h) (by
    exact mul_pos (mul_pos (mul_pos (mul_pos hfirst (pow_pos (by positivity) 3)) (hd s)) (hd t)) (hd u))

private theorem map_cliqueFree_three {α β : Type} (G : SimpleGraph α)
    (hG : G.CliqueFree 3) (f : α ↪ β) : (G.map f).CliqueFree 3 := by
  apply cliqueFree_of_no_triangle
  intro x y z hxy hxz hyz
  obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj f G _ _).1 hxy
  obtain ⟨a', c, hac, ha, rfl⟩ := (map_adj f G _ _).1 hxz
  cases f.injective ha
  exact no_triangle G hG hab hac (map_adj_apply.1 hyz)

private theorem reducedGraph_exists {α : Type} [Fintype α] (G : SimpleGraph α)
    (hG : G.CliqueFree 3) {e : ℝ} (he : 0 < e) (he₁ : e ≤ 1)
    (hn : ⌈4 / e⌉₊ ≤ Fintype.card α) :
    ∃ (H : SimpleGraph (Fin (SzemerediRegularity.bound (e / 8) ⌈4 / e⌉₊)))
      (color : α → Fin (SzemerediRegularity.bound (e / 8) ⌈4 / e⌉₊)),
      H.CliqueFree 3 ∧
      ∃ _ : DecidableRel (G \ H.comap color).Adj,
        (#(G \ H.comap color).edgeFinset : ℝ) < e * Fintype.card α ^ 2 := by
  classical
  have hl : 4 / e ≤ (⌈4 / e⌉₊ : ℕ) := Nat.le_ceil _
  haveI : Nonempty α := Fintype.card_pos_iff.mp (by
    have hpos : 0 < (⌈4 / e⌉₊ : ℕ) := Nat.ceil_pos.mpr (by positivity)
    omega)
  obtain ⟨P, hEq, hMin, hMax, hUnif⟩ := szemeredi_regularity G
    (by positivity : 0 < e / 8) hn
  let I := SzemerediRegularity.bound (e / 8) ⌈4 / e⌉₊
  let embed : P.parts ↪ Fin I :=
    (Fintype.equivFin P.parts).toEmbedding.trans (Fin.castLEEmb (by simpa [I] using hMax))
  let part (v : α) : P.parts := ⟨P.part v, P.part_mem.2 (mem_univ _)⟩
  let f := embed ∘ part
  let H := (clusterGraph G P e).map embed
  let R := G.regularityReduced P (e / 8) (e / 4)
  refine ⟨H, f, map_cliqueFree_three _ (clusterGraph_cliqueFree G hG P he he₁) _, inferInstance, ?_⟩
  have hR : R ≤ H.comap f := by
    intro x y hxy
    obtain ⟨_, X, hX, Y, hY, hx, hy, hXY, hu, hδ⟩ := hxy
    have hx' : P.part x = X := P.part_eq_of_mem hX hx
    have hy' : P.part y = Y := P.part_eq_of_mem hY hy
    exact map_adj_apply.2 ⟨fun h => hXY (hx'.symm.trans ((congrArg Subtype.val h).trans hy')),
      by simpa [part, hx', hy'] using hu, by simpa [part, hx', hy'] using hδ⟩
  have hle : (G \ H.comap f) ≤ (G \ R) := sdiff_le_sdiff_left hR
  have hCard : (#(G \ H.comap f).edgeFinset : ℝ) ≤ #(G \ R).edgeFinset :=
    Nat.cast_le.mpr (card_le_card (fun _ ha =>
      mem_edgeFinset.2 (edgeSet_subset_edgeSet.2 hle (mem_edgeFinset.1 ha))))
  have hsize := regularityReduced_edges_card_aux (G := G) he hEq hUnif
    (hl.trans (Nat.cast_le.mpr hMin))
  have hRle : R ≤ G := regularityReduced_le
  have hsize' : (#(G \ R).edgeFinset : ℝ) < e * Fintype.card α ^ 2 := by
    rw [edgeFinset_sdiff, cast_card_sdiff (edgeFinset_mono hRle)]
    change 2 * (#G.edgeFinset - #R.edgeFinset : ℝ) < 2 * e * (Fintype.card α ^ 2 : ℕ) at hsize
    push_cast at hsize
    linarith
  have eq : @edgeFinset α (G \ H.comap f) (G.fintypeEdgeSetSdiff (H.comap f)) =
      @edgeFinset α (G \ H.comap f) ((G \ H.comap f).fintypeEdgeSet) :=
    congrArg (fun t => @edgeFinset α (G \ H.comap f) t) (Subsingleton.elim _ _)
  rw [← eq]
  exact hCard.trans_lt hsize'

/-! ## The exceptional-vertex extension -/

def pullback {α β : Type} (Q : RankedOrder β) (f : α → β) : RankedOrder α where
  rank x := Q.rank (f x)
  rel x y := Q.rel (f x) (f y)
  rank_lt := Q.rank_lt
  trans := Q.trans

abbrev ExtendedLabels (β : Type) (k : ℕ) :=
  (β ⊕ Fin k) × Fin 3 × (Fin k → Bool) × (Fin k → Bool)

private def signatureOf {β : Type} {k : ℕ} (l : ExtendedLabels β k) :
    Signature β (Fin k) :=
  ⟨l.1.elim some (fun _ => none), l.2.1, {i | l.2.2.1 i = true}, {i | l.2.2.2 i = true}⟩

def exceptionHost {β : Type} (Q : RankedOrder β) (k : ℕ) :
    RankedOrder (ExtendedLabels β k) where
  rank l := (signatureOf l).rank
  rel x y := extensionRel Q (signatureOf x) (signatureOf y)
  rank_lt := fun h => h.1
  trans := extension_transitive Q

theorem exceptionHost_embeds {α β : Type} {P : RankedOrder α} {Q : RankedOrder β}
    (bad : α → Prop) {k : ℕ} (e : Subtype bad ↪ Fin k)
    (f : {x // ¬ bad x} → β) (hf : Induced (pullback P Subtype.val) Q f) :
    ∃ g : α → ExtendedLabels β k, Induced P (exceptionHost Q k) g := by
  classical
  let down (x : α) (i : Fin k) := ∃ a : Subtype bad, e a = i ∧ (a.val = x ∨ P.rel a.val x)
  let up (x : α) (i : Fin k) := ∃ a : Subtype bad, e a = i ∧ (x = a.val ∨ P.rel x a.val)
  let tag (x : α) : β ⊕ Fin k := if hx : bad x then .inr (e ⟨x, hx⟩) else .inl (f ⟨x, hx⟩)
  let g (x : α) : ExtendedLabels β k :=
    (tag x, P.rank x, fun i => decide (down x i), fun i => decide (up x i))
  have htag (x : α) (b : β) :
      (signatureOf (g x)).base = some b ↔ ∃ hx : ¬ bad x, f ⟨x, hx⟩ = b := by
    by_cases hx : bad x <;> simp [signatureOf, g, tag, hx]
  have hdown (x : α) (i : Fin k) : i ∈ (signatureOf (g x)).below ↔ down x i :=
    by simp [signatureOf, g]
  have hup (x : α) (i : Fin k) : i ∈ (signatureOf (g x)).above ↔ up x i :=
    by simp [signatureOf, g]
  refine ⟨g, ?_, ?_⟩
  · intro x y heq
    have ht : tag x = tag y := congrArg Prod.fst heq
    by_cases hx : bad x <;> by_cases hy : bad y <;> simp [tag, hx, hy] at ht
    · exact ht
    · exact congrArg Subtype.val (hf.1 ht)
  · intro x y
    change P.rel x y ↔ extensionRel Q (signatureOf (g x)) (signatureOf (g y))
    constructor
    · intro hxy
      refine ⟨P.rank_lt hxy, ?_, ?_, ?_⟩
      · intro i hi
        obtain ⟨a, ha, h | h⟩ := (hdown x i).1 hi
        · exact (hdown y i).2 ⟨a, ha, Or.inr (h ▸ hxy)⟩
        · exact (hdown y i).2 ⟨a, ha, Or.inr (P.trans h hxy)⟩
      · intro i hi
        obtain ⟨a, ha, h | h⟩ := (hup y i).1 hi
        · exact (hup x i).2 ⟨a, ha, Or.inr (h ▸ hxy)⟩
        · exact (hup x i).2 ⟨a, ha, Or.inr (P.trans hxy h)⟩
      · by_cases hx : bad x
        · exact Or.inr ⟨e ⟨x, hx⟩, (hup x _).2 ⟨⟨x, hx⟩, rfl, Or.inl rfl⟩,
            (hdown y _).2 ⟨⟨x, hx⟩, rfl, Or.inr hxy⟩⟩
        by_cases hy : bad y
        · exact Or.inr ⟨e ⟨y, hy⟩, (hup x _).2 ⟨⟨y, hy⟩, rfl, Or.inr hxy⟩,
            (hdown y _).2 ⟨⟨y, hy⟩, rfl, Or.inl rfl⟩⟩
        exact Or.inl ⟨_, _, (htag _ _).2 ⟨hx, rfl⟩, (htag _ _).2 ⟨hy, rfl⟩,
          (hf.2 ⟨x, hx⟩ ⟨y, hy⟩).1 hxy⟩
    · rintro ⟨hrank, _, _, ⟨a, b, ha, hb, hab⟩ | ⟨i, hi, hj⟩⟩
      · obtain ⟨hx, rfl⟩ := (htag _ _).1 ha
        obtain ⟨hy, rfl⟩ := (htag _ _).1 hb
        exact (hf.2 ⟨x, hx⟩ ⟨y, hy⟩).2 hab
      · obtain ⟨a, ha, hxa⟩ := (hup x i).1 hi
        obtain ⟨b, hb, hby⟩ := (hdown y i).1 hj
        cases e.injective (ha.trans hb.symm)
        rcases hxa with hx | hx <;> rcases hby with hy | hy
        · exact (ne_of_lt hrank (congrArg P.rank (hx.trans hy))).elim
        · exact hx ▸ hy
        · exact hy ▸ hx
        · exact P.trans hx hy

/-! ## The finite label space of a template -/

abbrev SmallSubsets (α : Type) [Fintype α] (d : ℕ) :=
  {s : Finset α // s.card ≤ d}

private theorem smallSubsets_card {α : Type} [Fintype α] (d : ℕ) :
    Fintype.card (SmallSubsets α d) = ∑ i ∈ range (d + 1), (Fintype.card α).choose i := by
  classical
  let e : SmallSubsets α d ≃ Σ i : Fin (d + 1), ↥((univ : Finset α).powersetCard i.val) :=
    { toFun := fun s => ⟨⟨s.val.card, by omega⟩, ⟨s.val, by simp⟩⟩
      invFun := fun s => ⟨s.2.val, by
        have hs := (mem_powersetCard.1 s.2.property).2
        have hi := s.1.isLt
        omega⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨i, hi⟩, ⟨s, hs⟩⟩
        have he : #s = i := (mem_powersetCard.1 hs).2
        subst i
        rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sigma, Fin.sum_univ_eq_sum_range]

abbrev CoreLabels (α : Type) [Fintype α] (k d : ℕ) :=
  α × (Fin k → Bool) × SmallSubsets α d

private theorem coreLabels_card {α : Type} [Fintype α] (k d : ℕ) :
    Fintype.card (CoreLabels α k d) =
      Fintype.card α * 2 ^ k *
        ∑ i ∈ range (d + 1), (Fintype.card α).choose i := by
  simp [CoreLabels, smallSubsets_card, Nat.mul_assoc]

variable {α : Type}

private def edgeAt {H : SimpleGraph α} {x y : α} (h : H.Adj x y) : H.edgeSet :=
  ⟨s(x, y), H.mem_edgeSet.2 h⟩

private theorem edgeAt_symm {H : SimpleGraph α} {x y : α} (h : H.Adj x y) :
    edgeAt h.symm = edgeAt h :=
  Subtype.ext (Sym2.eq_swap (a := y) (b := x))

private def Allocation.owns {H : SimpleGraph α} {k : ℕ} (A : Allocation H k)
    (x y : α) : Prop := ∃ h : H.Adj x y, (A.place (edgeAt h)).1 = x

private theorem Allocation.owns_either {H : SimpleGraph α} {k : ℕ} (A : Allocation H k)
    {x y : α} (h : H.Adj x y) : A.owns x y ∨ A.owns y x := by
  rcases Sym2.mem_iff.1 (A.endpoint (edgeAt h)) with hx | hy
  · exact Or.inl ⟨h, hx⟩
  · exact Or.inr ⟨h.symm, (congrArg (fun e => (A.place e).1) (edgeAt_symm h)).trans hy⟩

private def Allocation.reading {H : SimpleGraph α} {k : ℕ} (A : Allocation H k)
    (x y : α) : Readers where
  left := ¬ H.Adj x y ∨ A.owns x y
  right := ¬ H.Adj x y ∨ A.owns y x
  covers := by
    by_cases h : H.Adj x y
    · exact (A.owns_either h).imp Or.inr Or.inr
    · exact Or.inl (Or.inl h)

private theorem Allocation.single_imp_adj {H : SimpleGraph α} {k : ℕ} (A : Allocation H k)
    {x y : α} (h : (A.reading x y).single) : H.Adj x y := by
  classical
  by_contra hn
  exact h ⟨Or.inl hn, Or.inl hn⟩

private noncomputable def Allocation.unpack [Fintype α] {H : SimpleGraph α} {k d : ℕ}
    (A : Allocation H k) (l : CoreLabels α k d) : Label α := by
  classical
  exact ⟨l.1, fun y => if h : H.Adj l.1 y then
    l.2.1 (A.place (edgeAt h)).2 = true else y ∈ l.2.2.val⟩

private def decoderOrder (rank : α → Fin 3) (reading : α → α → Readers)
    (h : ∀ a m c : α, rank a = 0 → rank m = 1 → rank c = 2 →
      ¬ ((reading a m).single ∧ (reading m c).single ∧ (reading a c).single)) :
    RankedOrder (Label α) where
  rank x := rank x.slot
  rel := comparesUp rank reading
  rank_lt := fun h => h.1
  trans := decoder_transitive rank reading h

private noncomputable def coreHost [Fintype α] (rank : α → Fin 3) {H : SimpleGraph α}
    (hH : H.CliqueFree 3) {k : ℕ} (A : Allocation H k) (d : ℕ) :
    RankedOrder (CoreLabels α k d) :=
  pullback (decoderOrder rank A.reading (by
    rintro a m c _ _ _ ⟨am, mc, ac⟩
    exact no_triangle H hH (A.single_imp_adj am) (A.single_imp_adj ac) (A.single_imp_adj mc)))
    A.unpack

private theorem reads_congr (rank : α → Fin 3) (read : α → α → Readers)
    {x y : α} {p p' q q' : α → Prop}
    (hpl : ∀ z, (read x z).left → (p z ↔ p' z))
    (hpr : ∀ z, (read z x).right → (p z ↔ p' z))
    (hql : ∀ z, (read y z).left → (q z ↔ q' z))
    (hqr : ∀ z, (read z y).right → (q z ↔ q' z)) :
    comparesUp rank read ⟨x, p⟩ ⟨y, q⟩ ↔ comparesUp rank read ⟨x, p'⟩ ⟨y, q'⟩ := by
  classical
  have hlp (z : α) : leftPositive (read x z) (p z) ↔ leftPositive (read x z) (p' z) :=
    and_congr_right (hpl z)
  have hrp (z : α) : rightPositive (read z x) (p z) ↔ rightPositive (read z x) (p' z) :=
    and_congr_right (hpr z)
  have hlq (z : α) : leftPositive (read y z) (q z) ↔ leftPositive (read y z) (q' z) :=
    and_congr_right (hql z)
  have hrq (z : α) : rightPositive (read z y) (q z) ↔ rightPositive (read z y) (q' z) :=
    and_congr_right (hqr z)
  have hAccept : (read x y).allPositive (p y) (q x) ↔
      (read x y).allPositive (p' y) (q' x) :=
    and_congr (forall_congr' (hpl y)) (forall_congr' (hqr x))
  simp only [comparesUp, hAccept, hlp, hrp, hlq, hrq]

private theorem coreHost_embeds [Fintype α] (P : RankedOrder α)
    {H : SimpleGraph α} (hH : H.CliqueFree 3) {k d : ℕ} (A : Allocation H k)
    (dev : α → SmallSubsets α d)
    (hdev : ∀ x y, y ∈ (dev x).val ↔ (signedGraph P).Adj x y ∧ ¬ H.Adj x y) :
    ∃ f : α → CoreLabels α k d, Induced P (coreHost P.rank hH A d) f := by
  classical
  let f (x : α) : CoreLabels α k d :=
    (x, fun i => decide (∃ e : H.edgeSet, A.place e = (x, i) ∧ e.val ∈ (signedGraph P).edgeSet), dev x)
  have hSig (x y : α) (h : ¬H.Adj x y ∨ A.owns x y) :
      (A.unpack (f x)).positive y ↔ (encode P x).positive y := by
    have hgoal : (signedGraph P).Adj x y ↔ (encode P x).positive y := by
      rcases lt_trichotomy (P.rank x) (P.rank y) with hlt | heq | hgt
      · simp [signedGraph, encode, hlt, not_lt_of_gt hlt]
      · have hn : ¬ P.rel y x := fun h => (ne_of_lt (P.rank_lt h)) heq.symm
        have hf : ¬ (P.rank y = 0 ∧ P.rank y = 2) := by
          rintro ⟨h0, h2⟩
          exact (by decide : (0 : Fin 3) ≠ 2) (h0.symm.trans h2)
        simp [signedGraph, encode, graphBit, heq, hf, hn]
      · simp [signedGraph, encode, hgt, not_lt_of_gt hgt]
    rw [← hgoal]
    unfold Allocation.unpack
    simp only
    split
    · rename_i he
      have ho : (A.place (edgeAt he)).1 = x := by
        obtain ⟨he', ho⟩ := h.resolve_left (not_not_intro he)
        exact ho
      simp only [f, decide_eq_true_eq]
      constructor
      · rintro ⟨e, heq, hb⟩
        have ht : e = edgeAt he := A.place.injective (by
          rw [heq]
          exact Prod.ext ho.symm rfl)
        subst e
        exact (signedGraph P).mem_edgeSet.1 hb
      · intro hxy
        exact ⟨edgeAt he, Prod.ext ho rfl, (signedGraph P).mem_edgeSet.2 hxy⟩
    · rename_i hn
      simp only [f, hdev, hn, not_false_eq_true, and_true]
  refine ⟨f, fun _ _ h => congrArg Prod.fst h, ?_⟩
  intro x y
  have swap {u z : α} (h : (A.reading z u).right) :
      ¬H.Adj u z ∨ A.owns u z :=
    h.imp (fun hn had => hn had.symm) id
  have hc := reads_congr P.rank A.reading
    (fun z h => hSig x z h) (fun z h => hSig x z (swap h))
    (fun z h => hSig y z h) (fun z h => hSig y z (swap h))
  exact (hc.trans (decode_encode P A.reading x y)).symm

/-! ## Count the exceptional vertices and enumerate templates -/

private theorem highDegree_card_lt [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {ρ : ℝ} (hρ : 0 < ρ) (hn : 0 < Fintype.card α)
    (he : (#G.edgeFinset : ℝ) < ρ ^ 2 * Fintype.card α ^ 2) :
    letI := Classical.decPred (fun x => ⌊ρ * Fintype.card α⌋₊ < G.degree x)
    (Fintype.card {x // ⌊ρ * Fintype.card α⌋₊ < G.degree x} : ℝ) <
      2 * ρ * Fintype.card α := by
  classical
  let d := ⌊ρ * Fintype.card α⌋₊
  let S := univ.filter fun x => d < G.degree x
  have h₁ : #S * (d + 1) ≤ 2 * #G.edgeFinset := calc
    _ = ∑ _x ∈ S, (d + 1) := by simp
    _ ≤ ∑ x ∈ S, G.degree x := sum_le_sum (fun x hx => (mem_filter.1 hx).2)
    _ ≤ ∑ x, G.degree x :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
    _ = _ := G.sum_degrees_eq_twice_card_edges
  have h₂ : ρ * Fintype.card α ≤ (d : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have h₃ : (#S : ℝ) * (ρ * Fintype.card α) ≤ 2 * #G.edgeFinset := calc
    _ ≤ (#S : ℝ) * ((d : ℝ) + 1) := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast h₁
  have hmul : (#S : ℝ) * (ρ * Fintype.card α) <
      (2 * ρ * Fintype.card α) * (ρ * Fintype.card α) := by
    calc
      _ ≤ _ := h₃
      _ < 2 * (ρ ^ 2 * Fintype.card α ^ 2) := by linarith
      _ = _ := by ring
  have hsmall := lt_of_mul_lt_mul_right hmul (by positivity : 0 ≤ ρ * Fintype.card α)
  simpa [S, d, Fintype.card_subtype] using hsmall

private abbrev Colors (M : ℕ) := Fin M × Fin 3
private abbrev Counts (M n : ℕ) := Colors M → Fin (n + 1)
private abbrev Slots {M n : ℕ} (counts : Counts M n) :=
  Σ c : Colors M, Fin (counts c).val

private abbrev Template (M n : ℕ) :=
  {H : SimpleGraph (Fin M) // H.CliqueFree 3} ×
    {counts : Counts M n // Fintype.card (Slots counts) ≤ n}

private noncomputable instance (M n : ℕ) : Fintype (Template M n) := Fintype.ofFinite _

private abbrev TemplateSlots {M n : ℕ} (t : Template M n) := Slots t.2.val

private def slotGraph {M n : ℕ} (t : Template M n) : SimpleGraph (TemplateSlots t) :=
  t.1.val.comap fun x => x.1.1

private theorem slotGraph_cliqueFree {M n : ℕ} (t : Template M n) :
    (slotGraph t).CliqueFree 3 := by
  apply cliqueFree_of_no_triangle
  intro _ _ _ hxy hxz hyz
  exact no_triangle t.1.val t.1.property hxy hxz hyz

private noncomputable def templateAllocation {M n : ℕ} (t : Template M n) :
    Allocation (slotGraph t) ((n + 3) / 4) :=
  Classical.choice (allocation_exists (slotGraph t) (slotGraph_cliqueFree t)
    (t.2.property.trans (by omega)))

private noncomputable def templateHost {M n : ℕ} (t : Template M n) (d k : ℕ) :
    RankedOrder (ExtendedLabels (CoreLabels (TemplateSlots t) ((n + 3) / 4) d) k) :=
  exceptionHost (coreHost (fun x => x.1.2) (slotGraph_cliqueFree t) (templateAllocation t) d) k

private def sigmaUnion {ι : Type} {τ : ι → Type} (Q : ∀ i, RankedOrder (τ i)) :
    RankedOrder (Σ i, τ i) where
  rank x := (Q x.1).rank x.2
  rel x y := ∃ h : y.1 = x.1, (Q x.1).rel x.2 (h ▸ y.2)
  rank_lt := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h, hr⟩
    change j = i at h
    subst j
    exact (Q i).rank_lt hr
  trans := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨hij, hxy⟩ ⟨hjk, hyz⟩
    change j = i at hij
    change k = j at hjk
    subst j
    subst k
    exact ⟨rfl, (Q i).trans hxy hyz⟩

private theorem induced_sigmaUnion {ι α : Type} {τ : ι → Type}
    (Q : ∀ i, RankedOrder (τ i)) {P : RankedOrder α} {i : ι}
    {f : α → τ i} (hf : Induced P (Q i) f) :
    Induced P (sigmaUnion Q) (fun x => ⟨i, f x⟩) := by
  refine ⟨fun x y h => hf.1 (eq_of_heq (Sigma.mk.inj h).2), ?_⟩
  intro x y
  change P.rel x y ↔ ∃ h : i = i, (Q i).rel (f x) (h ▸ f y)
  rw [hf.2 x y]
  simp

private abbrev UniverseLabels (M n d k : ℕ) :=
  Σ t : Template M n, ExtendedLabels (CoreLabels (TemplateSlots t) ((n + 3) / 4) d) k

private noncomputable def universalHost (M n d k : ℕ) : RankedOrder (UniverseLabels M n d k) :=
  sigmaUnion (fun t => templateHost t d k)

private theorem canonicalSlots [Fintype α] {M n : ℕ} (hn : Fintype.card α ≤ n)
    (c : α → Colors M) :
    ∃ (counts : Counts M n) (e : α ≃ Slots counts),
      Fintype.card (Slots counts) ≤ n ∧ ∀ x, (e x).1 = c x := by
  classical
  let counts (j : Colors M) : Fin (n + 1) :=
    ⟨Fintype.card {a // c a = j}, Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans hn)⟩
  let e : α ≃ Slots counts := (Equiv.sigmaFiberEquiv c).symm.trans
    (Equiv.sigmaCongrRight fun j => Fintype.equivFin {a // c a = j})
  exact ⟨counts, e, (Fintype.card_congr e).ge.trans hn, fun _ => rfl⟩

private theorem templateHost_covers [Fintype α] (P : RankedOrder α) {M n d k : ℕ}
    (hn : Fintype.card α = n) (H : SimpleGraph (Fin M)) (hH : H.CliqueFree 3)
    (c : α → Fin M) (bad : α → Prop) (ebad : Subtype bad ↪ Fin k)
    (D : SimpleGraph α) [DecidableRel D.Adj] (hD : D = signedGraph P \ H.comap c)
    (hgood : ∀ x, ¬ bad x → D.degree x ≤ d) :
    ∃ f : α → UniverseLabels M n d k, Induced P (universalHost M n d k) f := by
  classical
  let Good := {x // ¬ bad x}
  let color (x : Good) : Colors M := (c x.val, P.rank x.val)
  obtain ⟨counts, e, hslots, hcol⟩ := canonicalSlots
    (α := Good) ((Fintype.card_subtype_le _).trans hn.le) color
  let t : Template M n := (⟨H, hH⟩, ⟨counts, hslots⟩)
  let orig (x : TemplateSlots t) : α := (e.symm x).val
  let Q := pullback P orig
  have hcolor (x : TemplateSlots t) : x.1 = (c (orig x), P.rank (orig x)) := by
    simpa [orig, color, t] using hcol (e.symm x)
  have hrank : Q.rank = fun x => x.1.2 := by
    funext x
    exact (congrArg Prod.snd (hcolor x)).symm
  have hadj (x y : TemplateSlots t) :
      D.Adj (orig x) (orig y) ↔ (signedGraph Q).Adj x y ∧ ¬ (slotGraph t).Adj x y := by
    rw [hD]
    change _ ∧ ¬ H.Adj (c (orig x)) (c (orig y)) ↔ _ ∧ ¬ H.Adj x.1.1 y.1.1
    rw [congrArg Prod.fst (hcolor x), congrArg Prod.fst (hcolor y)]
    rfl
  let dev (x : TemplateSlots t) := univ.filter fun y => D.Adj (orig x) (orig y)
  have hdev (x : TemplateSlots t) : #(dev x) ≤ d := by
    have hx : ¬ bad (orig x) := (e.symm x).property
    refine le_trans ?_ (hgood _ hx)
    apply card_le_card_of_injOn orig
    · intro y hy
      exact (D.mem_neighborFinset _ _).2 (mem_filter.1 hy).2
    · exact fun y z _ _ heq => e.symm.injective (Subtype.ext heq)
  obtain ⟨f, hf⟩ := coreHost_embeds Q (slotGraph_cliqueFree t) (templateAllocation t)
    (d := d) (fun x => ⟨dev x, hdev x⟩) (by simpa [dev] using hadj)
  rw [hrank] at hf
  have hf' : Induced (pullback P (Subtype.val : Good → α))
      (coreHost (fun x => x.1.2) (slotGraph_cliqueFree t) (templateAllocation t) d)
      (f ∘ e) := by
    refine ⟨hf.1.comp e.injective, fun x y => ?_⟩
    simpa [Q, orig, pullback] using hf.2 (e x) (e y)
  obtain ⟨g, hg⟩ := exceptionHost_embeds bad ebad (f ∘ e) hf'
  exact ⟨fun x => ⟨t, g x⟩, induced_sigmaUnion (fun t => templateHost t d k) hg⟩

private theorem universalHost_universal {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (hlarge : ⌈4 / ρ ^ 2⌉₊ ≤ n) :
    Universal n (universalHost (SzemerediRegularity.bound (ρ ^ 2 / 8) ⌈4 / ρ ^ 2⌉₊)
      n ⌊ρ * n⌋₊ ⌊2 * ρ * n⌋₊) := by
  classical
  intro α inst hcard P
  let G := signedGraph P
  have hε : ρ ^ 2 ≤ 1 := by nlinarith
  obtain ⟨H, c, hH, instD, hD⟩ :=
    reducedGraph_exists G (signedGraph_cliqueFree P) (sq_pos_of_pos hρ) hε (hcard ▸ hlarge)
  let D := G \ H.comap c
  letI : DecidableRel D.Adj := instD
  let d := ⌊ρ * n⌋₊
  let k := ⌊2 * ρ * n⌋₊
  let bad (x : α) := d < D.degree x
  have hsmall : (Fintype.card (Subtype bad) : ℝ) < 2 * ρ * n := by
    have h := highDegree_card_lt D hρ (hcard.symm ▸ hn) hD
    simpa only [bad, d, hcard] using h
  have hk : Fintype.card (Subtype bad) ≤ k := Nat.le_floor hsmall.le
  let e : Subtype bad ↪ Fin k :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hk))
  exact templateHost_covers P hcard H hH c bad e D rfl
    (fun _ hx => Nat.le_of_not_gt hx)

private noncomputable def graphCount (M : ℕ) : ℕ :=
  @Fintype.card (SimpleGraph (Fin M)) (Fintype.ofFinite _)

private theorem template_card_le (M n : ℕ) :
    Fintype.card (Template M n) ≤ graphCount M * (n + 1) ^ (3 * M) := by
  classical
  letI : Fintype (SimpleGraph (Fin M)) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective
    (fun t : Template M n => (t.1.val, t.2.val))
    (fun x y h => Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h)))
  simpa [graphCount, Fintype.card_fun, Nat.mul_comm M 3] using h

private abbrev binomialTail (n d : ℕ) : ℕ :=
  ∑ i ∈ range (d + 1), n.choose i

private theorem one_le_binomialTail (n d : ℕ) : 1 ≤ binomialTail n d := by
  simpa using (single_le_sum (f := n.choose) (fun _ _ => Nat.zero_le _)
    (mem_range.2 (Nat.zero_lt_succ d)))

private theorem extendedLabels_card {β : Type} [Fintype β] (k : ℕ) :
    Fintype.card (ExtendedLabels β k) = 3 * (Fintype.card β + k) * 2 ^ (2 * k) := by
  simp [ExtendedLabels, two_mul, pow_add]
  ring

private theorem universeLabels_card_le (M n d k : ℕ) (hk : k ≤ n) :
    Fintype.card (UniverseLabels M n d k) ≤
      graphCount M * (n + 1) ^ (3 * M) *
        (6 * n * 2 ^ ((n + 3) / 4) * binomialTail n d * 2 ^ (2 * k)) := by
  classical
  rw [Fintype.card_sigma]
  let E := n * 2 ^ ((n + 3) / 4) * binomialTail n d
  have hE : n ≤ E := calc
    _ = n * 1 * 1 := by simp
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by exact Nat.one_le_pow _ _ (by decide))) (one_le_binomialTail n d)
  have hn (t : Template M n) : Fintype.card (CoreLabels (TemplateSlots t) ((n + 3) / 4) d) ≤ E := by
    rw [coreLabels_card]
    apply Nat.mul_le_mul (Nat.mul_le_mul_right _ t.2.property)
    exact sum_le_sum (fun i _ => Nat.choose_le_choose i t.2.property)
  have hc (t : Template M n) :
      Fintype.card (ExtendedLabels (CoreLabels (TemplateSlots t) ((n + 3) / 4) d) k)
      ≤ 6 * E * 2 ^ (2 * k) := by
    rw [extendedLabels_card]
    have hh := Nat.mul_le_mul_right (2 ^ (2 * k))
      (Nat.mul_le_mul_left 3 (add_le_add (hn t) (hk.trans hE)))
    convert hh using 1; ring
  calc
    _ ≤ ∑ _ : Template M n, (6 * E * 2 ^ (2 * k)) := sum_le_sum (fun t _ => hc t)
    _ = Fintype.card (Template M n) * (6 * E * 2 ^ (2 * k)) := by simp
    _ ≤ _ := by
      convert Nat.mul_le_mul_right (6 * E * 2 ^ (2 * k)) (template_card_le M n) using 1;
        dsimp [E]; ring

/-! ## The sublinear overhead in the exponent -/

open Filter

private theorem binomialTail_le_exp {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    {n d : ℕ} (hd : d ≤ n) :
    (binomialTail n d : ℝ) ≤ Real.exp (t * n - Real.log t * d) := by
  have h₁ : (binomialTail n d : ℝ) * t ^ d ≤ (1 + t) ^ n := calc
    _ = ∑ i ∈ range (d + 1), (n.choose i : ℝ) * t ^ d := by
      simp only [binomialTail, Nat.cast_sum, sum_mul]
    _ ≤ ∑ i ∈ range (d + 1), (n.choose i : ℝ) * t ^ i := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ht.le ht₁ (Nat.le_of_lt_succ (mem_range.1 hi)))
        (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * t ^ i :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hd))
        (fun i _ _ => by positivity)
    _ = _ := by
      rw [show 1 + t = t + 1 by ring, add_pow]
      simp [mul_comm]
  have h₂ : (1 + t) ^ n ≤ Real.exp (t * n) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp t) _
  have hp : t ^ d = Real.exp (Real.log t * d) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log ht]
  rw [Real.exp_sub, ← hp, le_div_iff₀ (pow_pos ht d)]
  exact h₁.trans h₂

private theorem eventually_poly_le_exp (C : ℝ) (hC : 0 ≤ C) (p : ℕ) {a : ℝ}
    (ha : 0 < a) : ∃ N : ℕ, ∀ n ≥ N, C * ((n : ℝ) + 1) ^ p ≤ Real.exp (a * n) := by
  let B := (C + 1) * (2 : ℝ) ^ p
  have hB : 0 < B := by dsimp [B]; positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop p ha).bound
    (inv_pos.mpr hB)
  obtain ⟨z, hz⟩ := (eventually_atTop.1 h)
  refine ⟨max 1 ⌈z⌉₊, fun n hn => ?_⟩
  have h₁ : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (le_max_left 1 ⌈z⌉₊) hn)
  have hz' : z ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hn))
  have hx := hz (n : ℝ) hz'
  have hpow : 0 ≤ (n : ℝ) ^ p := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpow, abs_of_pos (Real.exp_pos _)] at hx
  calc
    _ ≤ (C + 1) * (2 * n : ℝ) ^ p := by
      gcongr <;> linarith
    _ = B * (n : ℝ) ^ p := by rw [mul_pow]; simp [B, mul_assoc]
    _ ≤ _ := by
      calc
        _ ≤ B * (B⁻¹ * Real.exp (a * n)) := mul_le_mul_of_nonneg_left hx hB.le
        _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]

private theorem ceil_quarter_bound (n : ℕ) :
    (2 : ℝ) ^ ((n + 3) / 4) ≤ 2 * Real.exp (Real.log 2 / 4 * n) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
  -- Rewrite only the constant prefactor back as an exponential.
  rw [Real.log_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : (↑((n + 3) / 4) : ℝ) * 4 ≤ (n : ℝ) + 3 := by
    exact_mod_cast (Nat.div_mul_le_self (n + 3) 4)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right h hl.le]

private theorem universalHost_size {a t ρ : ℝ} (ha : 0 < a) (ht : 0 < t) (ht₁ : t ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1 / 2)
    (hbudget : t + ρ * (-Real.log t + 4 * Real.log 2) ≤ a / 2) (M : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Fintype.card (UniverseLabels M n ⌊ρ * n⌋₊ ⌊2 * ρ * n⌋₊) : ℝ) ≤
        Real.exp ((Real.log 2 / 4 + a) * n) := by
  let C : ℝ := 12 * graphCount M
  obtain ⟨N, hN⟩ := eventually_poly_le_exp C (by dsimp [C]; positivity) (3 * M + 1)
    (by positivity : 0 < a / 2)
  refine ⟨N, fun n hn => ?_⟩
  let d := ⌊ρ * n⌋₊
  let k := ⌊2 * ρ * n⌋₊
  have hd : (d : ℝ) ≤ ρ * n := Nat.floor_le (by positivity)
  have hk : (k : ℝ) ≤ 2 * ρ * n := Nat.floor_le (by positivity)
  have hn₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hd' : d ≤ n := Nat.cast_le.mp (hd.trans (by
    simpa using (mul_le_mul_of_nonneg_right (hρ₁.trans (by norm_num : (1 : ℝ) / 2 ≤ 1)) hn₀)))
  have hk' : k ≤ n := Nat.cast_le.mp (hk.trans (by
    simpa using (mul_le_mul_of_nonneg_right (show 2 * ρ ≤ 1 by linarith) hn₀)))
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht₁
  have hb : (binomialTail n d : ℝ) ≤ Real.exp ((t - ρ * Real.log t) * n) := calc
    _ ≤ Real.exp (t * n - Real.log t * d) := binomialTail_le_exp ht ht₁ hd'
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonpos_left hd hlt])
  have hex : (2 : ℝ) ^ (2 * k) ≤ Real.exp ((4 * ρ * Real.log 2) * n) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    simp only [Real.log_exp, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hk hl₂.le])
  have hcount : (Fintype.card (UniverseLabels M n d k) : ℝ) ≤
      (graphCount M : ℝ) * ((n : ℝ) + 1) ^ (3 * M) *
        (6 * n * 2 ^ ((n + 3) / 4) * binomialTail n d * 2 ^ (2 * k)) := by
    exact_mod_cast universeLabels_card_le M n d k hk'
  calc
    _ ≤ _ := hcount
    _ ≤ (graphCount M : ℝ) * ((n : ℝ) + 1) ^ (3 * M) *
        (6 * (n + 1 : ℝ) * (2 * Real.exp (Real.log 2 / 4 * n)) *
           Real.exp ((t - ρ * Real.log t) * n) * Real.exp ((4 * ρ * Real.log 2) * n)) := by
      gcongr <;> first | exact ceil_quarter_bound n | linarith
    _ = C * ((n : ℝ) + 1) ^ (3 * M + 1) *
        Real.exp ((Real.log 2 / 4 + (t + ρ * (-Real.log t + 4 * Real.log 2))) * n) := by
      rw [pow_succ]
      have h : (Real.log 2 / 4 + (t + ρ * (-Real.log t + 4 * Real.log 2))) * n =
          (Real.log 2 / 4 * n + (t - ρ * Real.log t) * n) + (4 * ρ * Real.log 2) * n := by ring
      rw [h, Real.exp_add, Real.exp_add]
      dsimp [C]
      ring
    _ ≤ Real.exp (a / 2 * n) * Real.exp ((Real.log 2 / 4 + a / 2) * n) := by
      gcongr
      exact hN n hn
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- For each positive allowance in the exponent, all sufficiently large sizes admit
a height-at-most-three induced-universal host with at most (2^{(1/4+ε)n}) vertices. -/
theorem asymptotic_upper_bound : AsymptoticUpperBound := by
  classical
  intro ε hε
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  let a := ε * l
  have ha : 0 < a := mul_pos hε hl
  let t := min 1 (a / 4)
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht₁ : t ≤ 1 := min_le_left _ _
  let L := -Real.log t + 4 * l
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonpos ht.le ht₁]
  let ρ := min (1 / 2) (a / (4 * (L + 1)))
  have hden : 0 < 4 * (L + 1) := by positivity
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos ha hden)
  have hρ₁ : ρ ≤ 1 / 2 := min_le_left _ _
  have hρL : ρ * L ≤ a / 4 := by
    have h := (le_div_iff₀ hden).1 (min_le_right (1 / 2) (a / (4 * (L + 1))))
    have h' : ρ * (4 * (L + 1)) ≤ a := h
    nlinarith
  have ht' : t ≤ a / 4 := min_le_right _ _
  have hbudget : t + ρ * (-Real.log t + 4 * Real.log 2) ≤ a / 2 := by
    change t + ρ * L ≤ a / 2
    linarith
  let b := ⌈4 / ρ ^ 2⌉₊
  let M := SzemerediRegularity.bound (ρ ^ 2 / 8) b
  obtain ⟨N₀, hN₀⟩ := universalHost_size ha ht ht₁ hρ hρ₁ hbudget M
  refine ⟨max 1 (max b N₀), fun n hn => ?_⟩
  have hpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hn)
  have hlarge : b ≤ n := (le_max_left b N₀).trans ((le_max_right _ _).trans hn)
  have hsize := hN₀ n ((le_max_right b N₀).trans ((le_max_right _ _).trans hn))
  let β := UniverseLabels M n ⌊ρ * n⌋₊ ⌊2 * ρ * n⌋₊
  let Q := universalHost M n ⌊ρ * n⌋₊ ⌊2 * ρ * n⌋₊
  let e := Fintype.equivFin β
  refine ⟨Fintype.card β, pullback Q e.symm, ?_, ?_⟩
  · intro α inst hcard P
    obtain ⟨f, hf⟩ := universalHost_universal hρ hρ₁ hpos hlarge α hcard P
    exact ⟨e ∘ f, e.injective.comp hf.1, fun x y => by
      simpa [pullback] using hf.2 x y⟩
  · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    convert hsize using 2
    dsimp [a, l]
    ring


/-! ## Interpret the result for arbitrary strict orders -/

/-- Longest-chain ranks for a transitive relation that has no four-element chain. -/
noncomputable def rankOrderOf {α : Type} (r : α → α → Prop)
    (ht : ∀ {x y z}, r x y → r y z → r x z)
    (h₄ : ∀ a b c d, r a b → r b c → r c d → False) : RankedOrder α := by
  classical
  let rank (x : α) : Fin 3 :=
    if ∃ a b, r a b ∧ r b x then 2 else if ∃ a, r a x then 1 else 0
  refine ⟨rank, r, ?_, ht⟩
  intro x y hxy
  have hn : ¬ ∃ a b, r a b ∧ r b x := by
    rintro ⟨a, b, hab, hbx⟩
    exact h₄ a b x y hab hbx hxy
  have hy : ∃ b, r b y := ⟨x, hxy⟩
  by_cases hx : ∃ a, r a x
  · obtain ⟨a, hax⟩ := hx
    have hy₂ : ∃ a b, r a b ∧ r b y := ⟨a, x, hax, hxy⟩
    simp [rank, hn, show (∃ a, r a x) from ⟨a, hax⟩, hy₂]
  · by_cases hy₂ : ∃ a b, r a b ∧ r b y <;> simp [rank, hn, hx, hy, hy₂]

/-! ## Matching lower bound for connected pure height-three targets -/

/-- The comparability graph is connected and every maximal chain has three vertices. -/
def ConnectedPure {α : Type} (P : RankedOrder α) : Prop :=
  (∀ x y, Relation.ReflTransGen (fun a b => P.rel a b ∨ P.rel b a) x y) ∧
  (∀ s : Set α, IsMaxChain P.rel s → s.ncard = 3)

def UniversalConnectedPure {β : Type} (n : ℕ) (Q : RankedOrder β) : Prop :=
  ∀ (α : Type) [Fintype α], Fintype.card α = n →
    ∀ P : RankedOrder α, ConnectedPure P → ∃ f : α → β, Induced P Q f

private abbrev CountingSlots (a b : ℕ) := Unit ⊕ (Option (Fin a) ⊕ Option (Fin b))

private def baseVertex {a b : ℕ} : CountingSlots a b := .inl ()
private def midVertex {a b : ℕ} (x : Option (Fin a)) : CountingSlots a b := .inr (.inl x)
private def topVertex {a b : ℕ} (x : Option (Fin b)) : CountingSlots a b := .inr (.inr x)

private def pureBits {a b : ℕ} (bits : Fin a × Fin b → Bool) : RankedOrder (CountingSlots a b) where
  rank
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr _) => 2
  rel
    | .inl _, .inr _ => True
    | .inr (.inl i), .inr (.inr j) =>
      match i, j with
      | some i, some j => bits (i, j) = true
      | _, _ => True
    | _, _ => False
  rank_lt := by
    intro x y h
    obtain (x | (i | i)) := x <;> obtain (y | (j | j)) := y <;>
      simp only at h ⊢ <;> first | contradiction | decide
  trans := by
    intro x y z hxy hyz
    obtain (x | (i | i)) := x <;> obtain (y | (j | j)) := y <;>
      obtain (z | (k | k)) := z <;> simp only at hxy hyz ⊢

private theorem pureBits_connectedPure {a b : ℕ} (bits : Fin a × Fin b → Bool) :
    ConnectedPure (pureBits bits) := by
  classical
  let P := pureBits bits
  refine ⟨?_, ?_⟩
  · have hb (x : CountingSlots a b) :
        Relation.ReflTransGen (fun p q => P.rel p q ∨ P.rel q p) baseVertex x := by
      obtain (⟨⟩ | x) := x
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (Or.inl trivial)
    have hb' (x : CountingSlots a b) :
        Relation.ReflTransGen (fun p q => P.rel p q ∨ P.rel q p) x baseVertex := by
      obtain (⟨⟩ | x) := x
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (Or.inr trivial)
    exact fun x y => (hb' x).trans (hb y)
  · have extend : ∀ s : Finset (CountingSlots a b), IsChain P.rel (s : Set (CountingSlots a b)) →
        ∃ a m c, P.rel a m ∧ P.rel m c ∧ ∀ x ∈ s, x = a ∨ x = m ∨ x = c := by
      intro s hs
      have pick {γ : Type} (v : γ → CountingSlots a b) (hv : Function.Injective v)
          (fixed : γ) (hr : ∀ j, P.rank (v j) = P.rank (v fixed)) :
          ∃ i, (v i ∈ s ∨ i = fixed) ∧ (∀ j, v j ∈ s → j = i) := by
        by_cases he : ∃ i, v i ∈ s
        · obtain ⟨i, hi⟩ := he
          refine ⟨i, Or.inl hi, fun j hj => ?_⟩
          by_contra hne
          have h := hs hj hi (hv.ne hne)
          rcases h with h | h
          · exact (P.rank_lt h).ne ((hr j).trans (hr i).symm)
          · exact (P.rank_lt h).ne ((hr i).trans (hr j).symm)
        · exact ⟨fixed, Or.inr rfl, fun i hi => (he ⟨i, hi⟩).elim⟩
      obtain ⟨i, hi, hi'⟩ := pick midVertex (fun _ _ h => Sum.inl.inj (Sum.inr.inj h)) none
        (fun _ => rfl)
      obtain ⟨j, hj, hj'⟩ := pick topVertex (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)) none
        (fun _ => rfl)
      refine ⟨baseVertex, midVertex i, topVertex j, trivial, ?_, ?_⟩
      · rcases hi with hi | rfl
        · rcases hj with hj | rfl
          · exact (hs hi hj (by simp [midVertex, topVertex])).resolve_right
              (fun h => (by decide : ¬ (2 : Fin 3) < 1) (P.rank_lt h))
          · cases i <;> trivial
        · exact True.intro
      · intro x hx
        obtain (⟨⟩ | (i' | j')) := x
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (congrArg midVertex (hi' i' hx)))
        · exact Or.inr (Or.inr (congrArg topVertex (hj' j' hx)))
    intro s hs
    let sf := s.toFinset
    obtain ⟨x, y, z, hxy, hyz, hmem⟩ := extend sf (by simpa [sf] using hs.1)
    have hxz := P.trans hxy hyz
    have hc : IsChain P.rel ({x, y, z} : Set (CountingSlots a b)) := by
      apply (IsChain.pair hyz).insert
      intro v hv _
      rcases Set.mem_insert_iff.1 hv with rfl | hv
      · exact Or.inl hxy
      · obtain rfl := Set.mem_singleton_iff.1 hv
        exact Or.inl hxz
    have hes := hs.2 hc (by
      intro v hv
      rcases hmem v (by simpa [sf] using hv) with rfl | rfl | rfl <;> simp)
    exact Set.ncard_eq_three.2
      ⟨x, y, z, (P.rank_lt hxy).ne.imp (congrArg P.rank),
        (P.rank_lt hxz).ne.imp (congrArg P.rank), (P.rank_lt hyz).ne.imp (congrArg P.rank), hes⟩

theorem connected_pure_counting_lower_bound {a b : ℕ} {β : Type} [Fintype β]
    {Q : RankedOrder β} (hQ : UniversalConnectedPure (a + b + 3) Q) :
    2 ^ (a * b) ≤ (Fintype.card β) ^ (a + b + 3) := by
  classical
  have hc : Fintype.card (CountingSlots a b) = a + b + 3 := by
    simp [CountingSlots]
    omega
  have embeds : ∀ bits : (Fin a × Fin b) → Bool,
      ∃ f : CountingSlots a b → β, Induced (pureBits bits) Q f :=
    fun bits => hQ _ hc _ (pureBits_connectedPure bits)
  choose f hf using embeds
  have hinj : Function.Injective f := by
    intro lhs rhs h
    funext ij
    obtain ⟨i, j⟩ := ij
    have hL := (hf lhs).2 (midVertex (some i)) (topVertex (some j))
    have hR := (hf rhs).2 (midVertex (some i)) (topVertex (some j))
    rw [h] at hL
    have hbits : lhs (i, j) = true ↔ rhs (i, j) = true := hL.trans hR.symm
    cases hi : lhs (i, j) <;> cases hj : rhs (i, j) <;> simp_all
  simpa [Fintype.card_fun, hc] using Fintype.card_le_of_injective _ hinj

theorem connected_pure_lower_bound {n : ℕ} {β : Type} [Fintype β]
    {Q : RankedOrder β} (hn : 6 ≤ n) (hQ : UniversalConnectedPure n Q) :
    2 ^ (n / 4 - 2) ≤ Fintype.card β := by
  let q := n / 4 - 2
  let a := 2 * q
  let b := n - 3 - a
  have hab : a + b + 3 = n := by dsimp [a, b, q]; omega
  have hnb : n ≤ 2 * b := by dsimp [b, a, q]; omega
  have hprod : q * n ≤ a * b := calc
    _ ≤ q * (2 * b) := Nat.mul_le_mul_left _ hnb
    _ = _ := by dsimp [a]; ring
  have hcount := connected_pure_counting_lower_bound (a := a) (b := b) (Q := Q)
    (by simpa only [hab] using hQ)
  rw [hab] at hcount
  have hpower : (2 ^ q) ^ n ≤ (Fintype.card β) ^ n := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hprod).trans hcount
  by_contra! h
  exact (not_lt_of_ge hpower) (Nat.pow_lt_pow_left h (by omega))

/-- The same host gives the asymptotic upper bound on the connected pure subfamily. -/
theorem connected_pure_asymptotic_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ N : ℕ, ∃ Q : RankedOrder (Fin N),
        UniversalConnectedPure n Q ∧ (N : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * (n : ℝ)) := by
  intro ε hε
  obtain ⟨n₀, h⟩ := asymptotic_upper_bound ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨N, Q, hQ, hSize⟩ := h n hn
  exact ⟨N, Q, fun α _ hc P _ => hQ α hc P, hSize⟩

end HeightThree
