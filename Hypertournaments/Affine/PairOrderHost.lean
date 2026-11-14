import Hypertournaments.Affine.PairLanguage
import Hypertournaments.Affine.LabelledAmalgamation
import Hypertournaments.AllOrderHost
import Hypertournaments.OrderedStrongSpan
import Mathlib.Tactic.Ext

/-!
# Ordered joint hosts for independent involutive labels

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the affine potential construction. Both arities strongly amalgamate on the
same exact-overlap carrier. Finite joint hosts then contain every freely
ordered presentation, and, for finite palettes, every labelled pair on a
specified finite source carrier. Empty carriers and empty index families
are included.
-/

universe u₁ u₂ v w

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

noncomputable section

/-- Both independent arities strongly amalgamate together with the given orders. -/
theorem pair_ordered_strong_span {r : ℕ} {Q : Type u₁} {K : Type u₂}
    [Nonempty Q] [Nonempty K] {P : Palette Q} {R : Palette K}
    {A B C : Type v} [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Pair r P R A) (BB : Pair r P R B) (CC : Pair r P R C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : AA.Preserves BB f.toEmbedding) (hAC : AA.Preserves CC g.toEmbedding) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Pair r P R (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      BB.Preserves D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      CC.Preserves D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨low, hlowL, hlowR⟩ := labelled_strong_span AA.low BB.low CC.low
    f.toEmbedding g.toEmbedding hAB.1 hAC.1
  obtain ⟨high, hhighL, hhighR⟩ := labelled_strong_span AA.high BB.high CC.high
    f.toEmbedding g.toEmbedding hAB.2 hAC.2
  obtain ⟨order, hi, hj⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  exact ⟨order, ⟨low, high⟩, ⟨hlowL, hhighL⟩, ⟨hlowR, hhighR⟩, hi, hj⟩

private def emptyPair (r : ℕ) (hr : 0 < r) {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) : Pair r P R PEmpty.{v + 1} where
  low := {
    label := fun t => PEmpty.elim (t ⟨0, hr⟩)
    swap_label := fun t _ _ _ => PEmpty.elim (t ⟨0, hr⟩) }
  high := {
    label := fun t => PEmpty.elim (t ⟨0, Nat.zero_lt_succ r⟩)
    swap_label := fun t _ _ _ => PEmpty.elim (t ⟨0, Nat.zero_lt_succ r⟩) }

/-- Ordered joint embeddings use the actual common empty structure. -/
theorem pair_ordered_jointEmbedding {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K)
    {V W : Type v} [Finite V] [Finite W]
    (A : Pair r P R V) (B : Pair r P R W) (orderA : LinearOrder V) (orderB : LinearOrder W) :
    ∃ (X : Type v) (_ : Finite X) (D : Pair r P R X) (orderD : LinearOrder X),
      Nonempty (Embedding (toOrderedPair A orderA) (toOrderedPair D orderD)) ∧
      Nonempty (Embedding (toOrderedPair B orderB) (toOrderedPair D orderD)) := by
  classical
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 2) hr
  let E : Pair r P R PEmpty.{v + 1} := emptyPair r hrpos P R
  let : LinearOrder PEmpty.{v + 1} := LinearOrder.ofSubsingleton
  let : LinearOrder V := orderA
  let : LinearOrder W := orderB
  let f : PEmpty.{v + 1} ↪o V := OrderEmbedding.ofStrictMono
    (Function.Embedding.ofIsEmpty : PEmpty.{v + 1} ↪ V) (fun x => PEmpty.elim x)
  let g : PEmpty.{v + 1} ↪o W := OrderEmbedding.ofStrictMono
    (Function.Embedding.ofIsEmpty : PEmpty.{v + 1} ↪ W) (fun x => PEmpty.elim x)
  have hf : E.Preserves A f.toEmbedding :=
    ⟨fun t => PEmpty.elim (t ⟨0, hrpos⟩),
      fun t => PEmpty.elim (t ⟨0, Nat.zero_lt_succ r⟩)⟩
  have hg : E.Preserves B g.toEmbedding :=
    ⟨fun t => PEmpty.elim (t ⟨0, hrpos⟩),
      fun t => PEmpty.elim (t ⟨0, Nat.zero_lt_succ r⟩)⟩
  obtain ⟨orderD, D, hi, hj, hiOrder, hjOrder⟩ :=
    pair_ordered_strong_span E A B f g hf hg
  let X := FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding
  let i : @OrderEmbedding V X orderA.toLE orderD.toLE :=
    @OrderEmbedding.ofStrictMono V X orderA orderD.toPreorder
      (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) hiOrder
  let j : @OrderEmbedding W X orderB.toLE orderD.toLE :=
    @OrderEmbedding.ofStrictMono W X orderB orderD.toPreorder
      (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) hjOrder
  exact ⟨X, inferInstance, D, orderD,
    ⟨@pairOrderedEmbedding r Q K P R V X orderA orderD A D i hi⟩,
    ⟨@pairOrderedEmbedding r Q K P R W X orderB orderD B D j hj⟩⟩

/-- A finite indexed family has one actual ordered host retaining an anchor. -/
theorem finite_pair_ordered_jointEmbedding {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K)
    {I : Type w} (indices : Finset I) (Carrier : I → Type v)
    (models : ∀ i, Pair r P R (Carrier i)) (orders : ∀ i, LinearOrder (Carrier i))
    (hfinite : ∀ i, Finite (Carrier i))
    {U : Type v} [Finite U] (anchor : Pair r P R U) (orderAnchor : LinearOrder U) :
    ∃ (X : Type v) (_ : Finite X) (D : Pair r P R X) (orderD : LinearOrder X),
      Nonempty (Embedding (toOrderedPair anchor orderAnchor) (toOrderedPair D orderD)) ∧
      ∀ i ∈ indices,
        Nonempty (Embedding (toOrderedPair (models i) (orders i)) (toOrderedPair D orderD)) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    exact ⟨U, inferInstance, anchor, orderAnchor, ⟨Embedding.id _⟩, by simp⟩
  | @insert i indices hi ih =>
    obtain ⟨X, hX, D, orderD, ⟨eAnchor⟩, hEach⟩ := ih
    let : Finite X := hX
    let : Finite (Carrier i) := hfinite i
    obtain ⟨Y, hY, E, orderE, ⟨eD⟩, ⟨eI⟩⟩ :=
      pair_ordered_jointEmbedding hr P R D (models i) orderD (orders i)
    refine ⟨Y, hY, E, orderE, ⟨eD.comp eAnchor⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨eI⟩
    · obtain ⟨ej⟩ := hEach j hj
      exact ⟨eD.comp ej⟩

/-- A finite index type can be joined without selecting an enumeration. -/
theorem all_finite_pair_ordered_jointEmbedding {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K)
    {I : Type w} [Finite I] (Carrier : I → Type v)
    (models : ∀ i, Pair r P R (Carrier i)) (orders : ∀ i, LinearOrder (Carrier i))
    (hfinite : ∀ i, Finite (Carrier i))
    {U : Type v} [Finite U] (anchor : Pair r P R U) (orderAnchor : LinearOrder U) :
    ∃ (X : Type v) (_ : Finite X) (D : Pair r P R X) (orderD : LinearOrder X),
      Nonempty (Embedding (toOrderedPair anchor orderAnchor) (toOrderedPair D orderD)) ∧
      ∀ i, Nonempty (Embedding (toOrderedPair (models i) (orders i)) (toOrderedPair D orderD)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨X, hX, D, orderD, hAnchor, hEach⟩ :=
    finite_pair_ordered_jointEmbedding hr P R Finset.univ Carrier models orders hfinite
      anchor orderAnchor
  exact ⟨X, hX, D, orderD, hAnchor, fun i => hEach i (Finset.mem_univ i)⟩

/-- Reindexing through an order isomorphism retains both intrinsic labels. -/
def pairOrderExpansionReindex {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} [Fintype V]
    (A : Pair r P R V) (canonical orderA : LinearOrder V) :
    Embedding (toOrderedPair A orderA)
      (toOrderedPair (A.pullback
        (Hypertournaments.Ramsey.orderChange canonical orderA).toEquiv.toEmbedding) canonical) := by
  let σ := Hypertournaments.Ramsey.orderChange canonical orderA
  let e : @OrderEmbedding V V orderA.toLE canonical.toLE :=
    @OrderIso.toOrderEmbedding V V orderA.toLE canonical.toLE
      (@OrderIso.symm V V canonical.toLE orderA.toLE σ)
  apply @pairOrderedEmbedding r Q K P R V V orderA canonical A
    (A.pullback σ.toEquiv.toEmbedding) e
  constructor <;> intro t
  · change A.low.label ((t.trans e.toEmbedding).trans σ.toEquiv.toEmbedding) = A.low.label t
    congr 1
    ext k
    exact σ.toEquiv.apply_symm_apply (t k)
  · change A.high.label ((t.trans e.toEmbedding).trans σ.toEquiv.toEmbedding) = A.high.label t
    congr 1
    ext k
    exact σ.toEquiv.apply_symm_apply (t k)

/-- One fixed finite host contains every free order of A and a supplied anchor. -/
theorem exists_all_pair_order_host_with {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K)
    {V U : Type v} [Finite V] [Finite U]
    (A : Pair r P R V) (anchor : Pair r P R U) (orderAnchor : LinearOrder U) :
    ∃ (W : Type v) (_ : Finite W) (D : Pair r P R W) (orderD : LinearOrder W),
      (∀ orderA : LinearOrder V,
        Nonempty (Embedding (toOrderedPair A orderA) (toOrderedPair D orderD))) ∧
      Nonempty (Embedding (toOrderedPair anchor orderAnchor) (toOrderedPair D orderD)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' e e.injective
  let models : Equiv.Perm V → Pair r P R V := fun σ => A.pullback σ.toEmbedding
  obtain ⟨W, hW, D, orderD, hAnchor, hEach⟩ :=
    all_finite_pair_ordered_jointEmbedding hr P R (fun _ : Equiv.Perm V => V)
      models (fun _ => canonical) (fun _ => inferInstance) anchor orderAnchor
  refine ⟨W, hW, D, orderD, ?_, hAnchor⟩
  intro orderA
  let σ := (Hypertournaments.Ramsey.orderChange canonical orderA).toEquiv
  obtain ⟨j⟩ := hEach σ
  exact ⟨j.comp (pairOrderExpansionReindex A canonical orderA)⟩

/-- Finite palettes give a common host for every pair on the fixed finite
source carrier, with every free order, while retaining an arbitrary anchor. -/
theorem exists_all_pair_models_order_host_with {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Finite Q] [Finite K] [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K)
    {V U : Type v} [Finite V] [Finite U]
    (anchor : Pair r P R U) (orderAnchor : LinearOrder U) :
    ∃ (W : Type v) (_ : Finite W) (D : Pair r P R W) (orderD : LinearOrder W),
      (∀ (A : Pair r P R V) (orderA : LinearOrder V),
        Nonempty (Embedding (toOrderedPair A orderA) (toOrderedPair D orderD))) ∧
      Nonempty (Embedding (toOrderedPair anchor orderAnchor) (toOrderedPair D orderD)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' e e.injective
  obtain ⟨W, hW, D, orderD, hAnchor, hEach⟩ :=
    all_finite_pair_ordered_jointEmbedding hr P R (fun _ : Pair r P R V => V)
      (fun A => A) (fun _ => canonical) (fun _ => inferInstance) anchor orderAnchor
  refine ⟨W, hW, D, orderD, ?_, hAnchor⟩
  intro A orderA
  let σ := (Hypertournaments.Ramsey.orderChange canonical orderA).toEquiv
  obtain ⟨j⟩ := hEach (A.pullback σ.toEmbedding)
  exact ⟨j.comp (pairOrderExpansionReindex A canonical orderA)⟩

end

end Hypertournaments.Affine
