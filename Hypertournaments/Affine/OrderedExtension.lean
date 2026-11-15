import Hypertournaments.Affine.OrderedLabels
import Hypertournaments.OrderedStrongSpan
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# Ordered extensions and points between each original pair

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the ordering property in `Further potential constructions`.
Mixed subsets receive a fixed label. In particular, inserted points can
give one common ordered edge type on both halves of every original pair.
-/

namespace Hypertournaments.Affine

universe u v w

noncomputable section

/-- Extend along an ordered injection, giving all other subsets a fallback label. -/
def Labelled.extendOrdered {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} {W : Type w} [LinearOrder V] [LinearOrder W]
    (A : Labelled n P V) (e : V ↪o W) (fallback : Q) : Labelled n P W := by
  classical
  exact Labelled.fromOrderedLabels P (fun S =>
    if h : ∃ T : Finset V, T.image e = S then A.canonicalTable fallback (Classical.choose h)
      else fallback)

theorem Labelled.extendOrdered_preserves {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} {W : Type w} [LinearOrder V] [LinearOrder W]
    (A : Labelled n P V) (e : V ↪o W) (fallback : Q) :
    A.Preserves (A.extendOrdered e fallback) e.toEmbedding := by
  classical
  have ht (S : Finset V) :
      (if h : ∃ T : Finset V, T.image e = S.image e then
        A.canonicalTable fallback (Classical.choose h) else fallback) =
      A.canonicalTable fallback S := by
    have h : ∃ T : Finset V, T.image e = S.image e := ⟨S, rfl⟩
    rw [dite_eq_left h]
    have heq : Classical.choose h = S :=
      (Finset.image_injective e.injective) (Classical.choose_spec h)
    rw [heq]
  have h := fromOrderedLabels_preserves (n := n) P e (A.canonicalTable fallback)
    (fun S => if h : ∃ T : Finset V, T.image e = S then
      A.canonicalTable fallback (Classical.choose h) else fallback) ht
  intro t
  exact (h t).trans (A.from_canonicalTable_label fallback t)

/-- A genuinely new vertex makes an increasing tuple receive the fallback label. -/
theorem Labelled.extendOrdered_label {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} {W : Type w} [LinearOrder V] [LinearOrder W]
    (A : Labelled n P V) (e : V ↪o W) (fallback : Q) (t : Fin n ↪ W)
    (ht : StrictMono (t : Fin n → W)) (hnew : ∃ i, t i ∉ Set.range e) :
    (A.extendOrdered e fallback).label t = fallback := by
  classical
  change (Labelled.fromOrderedLabels P _).label t = fallback
  rw [fromOrderedLabels_label_strictMono P _ t ht]
  have hn : ¬ ∃ T : Finset V, T.image e = tupleVertices t := by
    rintro ⟨T, hT⟩
    obtain ⟨i, hi⟩ := hnew
    have hmem : t i ∈ T.image e := by
      rw [hT]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
    exact hi ⟨x, hx⟩
  exact dite_eq_right hn

/-- One point is inserted for every strict original pair. -/
abbrev OrderWitness {V : Type v} [LinearOrder V] := {p : V × V // p.1 < p.2}

abbrev OrderWitnessCarrier (V : Type v) [LinearOrder V] := V ⊕ OrderWitness (V := V)

instance {V : Type v} [LinearOrder V] [Finite V] : Finite (OrderWitnessCarrier V) := by
  dsimp [OrderWitnessCarrier, OrderWitness]
  infer_instance

private def orderWitnessKey {V : Type v} [LinearOrder V] [Finite V]
    (x : OrderWitnessCarrier V) : ℕ ×ₗ Fin (Nat.card (OrderWitnessCarrier V)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let first : ℕ := match x with
    | .inl v => 2 * OrderedStrongSpan.pointRank V v
    | .inr p => 2 * OrderedStrongSpan.pointRank V p.1.1 + 1
  exact toLex (first, finiteIndex x)
where
  finiteIndex {V : Type v} [LinearOrder V] [Finite V] :
      OrderWitnessCarrier V ≃ Fin (Nat.card (OrderWitnessCarrier V)) := by
    let : Fintype (OrderWitnessCarrier V) := Fintype.ofFinite _
    exact Fintype.equivFinOfCardEq (by simp only [Nat.card_eq_fintype_card])

/-- Old points have even rank keys; a witness after x has the following odd key. -/
@[instance_reducible] def orderWitnessOrder (V : Type v) [LinearOrder V] [Finite V] :
    LinearOrder (OrderWitnessCarrier V) :=
  LinearOrder.lift' orderWitnessKey (by
    intro x y h
    exact orderWitnessKey.finiteIndex.injective
      (congrArg (fun z => (ofLex z).2) h))

theorem orderWitness_old_strictMono {V : Type v} [LinearOrder V] [Finite V] :
    @StrictMono V (OrderWitnessCarrier V) inferInstance (orderWitnessOrder V).toPreorder
      (Sum.inl : V → OrderWitnessCarrier V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro x y hxy
  change orderWitnessKey (.inl x) < orderWitnessKey (.inl y)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  have h := OrderedStrongSpan.pointRank_strictMono V hxy
  change 2 * OrderedStrongSpan.pointRank V x < 2 * OrderedStrongSpan.pointRank V y
  omega

theorem orderWitness_lower {V : Type v} [LinearOrder V] [Finite V]
    (p : OrderWitness (V := V)) :
    @LT.lt (OrderWitnessCarrier V) (orderWitnessOrder V).toLT (.inl p.1.1) (.inr p) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  change orderWitnessKey (.inl p.1.1) < orderWitnessKey (.inr p)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  change 2 * OrderedStrongSpan.pointRank V p.1.1 < 2 * OrderedStrongSpan.pointRank V p.1.1 + 1
  omega

theorem orderWitness_upper {V : Type v} [LinearOrder V] [Finite V]
    (p : OrderWitness (V := V)) :
    @LT.lt (OrderWitnessCarrier V) (orderWitnessOrder V).toLT (.inr p) (.inl p.1.2) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  change orderWitnessKey (.inr p) < orderWitnessKey (.inl p.1.2)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  have h := OrderedStrongSpan.pointRank_strictMono V p.2
  change 2 * OrderedStrongSpan.pointRank V p.1.1 + 1 < 2 * OrderedStrongSpan.pointRank V p.1.2
  omega

end

end Hypertournaments.Affine
