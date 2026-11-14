import Hypertournaments.Affine.PairLanguage
import Hypertournaments.Affine.OrderedExtension
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# One ordered edge type detects the order of every original pair

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the expansion property in `Further potential constructions`.
An inserted point between each original pair makes both new edges have
one fixed type. Homogeneity of that single type therefore controls the old order.
-/

namespace Hypertournaments.Affine

universe u₁ u₂ v w

open StructuralRamsey
open StructuralRamsey.Structure

noncomputable section

def Pair.extendOrdered {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W] (A : Pair r P R V) (e : V ↪o W)
    (q : Q) (k : K) : Pair r P R W where
  low := A.low.extendOrdered e q
  high := A.high.extendOrdered e k

theorem Pair.extendOrdered_preserves {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W] (A : Pair r P R V) (e : V ↪o W)
    (q : Q) (k : K) : A.Preserves (A.extendOrdered e q k) e.toEmbedding :=
  ⟨A.low.extendOrdered_preserves e q, A.high.extendOrdered_preserves e k⟩

def pairEdgeModel (r : ℕ) {Q : Type u₁} {K : Type u₂} (P : Palette Q) (R : Palette K)
    (q : Q) (k : K) : Pair r P R (Fin 2) where
  low := Labelled.fromOrderedLabels P (fun _ => q)
  high := Labelled.fromOrderedLabels R (fun _ => k)

def orderedPairEdgeModel (r : ℕ) {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) (q : Q) (k : K) :
    Structure (orderedPairLanguage r P R) (Fin 2) :=
  toOrderedPair (pairEdgeModel r P R q k) inferInstance

/-- A mixed increasing edge has the chosen edge type, also in the binary base case. -/
theorem pairEdgeModel_preserves_extend {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} {P : Palette Q} {R : Palette K}
    {V : Type v} {W : Type w} [LinearOrder V] [LinearOrder W]
    (A : Pair r P R V) (j : V ↪o W) (q : Q) (k : K) (e : Fin 2 ↪o W)
    (hnew : ∃ i, e i ∉ Set.range j) :
    (pairEdgeModel r P R q k).Preserves (A.extendOrdered j q k) e.toEmbedding := by
  constructor
  · by_cases heqr : r = 2
    · subst r
      apply Labelled.preserves_of_canonical
      intro S hS
      have hid : (S.orderEmbOfFin hS).toEmbedding = Function.Embedding.refl (Fin 2) := by
        ext i
        exact congrArg Fin.val (congrFun (S.orderEmbOfFin hS).strictMono.eq_id i)
      change (A.low.extendOrdered j q).label ((S.orderEmbOfFin hS).toEmbedding.trans e.toEmbedding) =
        (Labelled.fromOrderedLabels P (fun _ : Finset (Fin 2) => q)).label
          (S.orderEmbOfFin hS).toEmbedding
      rw [fromOrderedLabels_label_strictMono P _ _ (S.orderEmbOfFin hS).strictMono, hid]
      exact A.low.extendOrdered_label j q e.toEmbedding e.strictMono hnew
    · intro t
      have hcard := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at hcard
      omega
  · intro t
    have hcard := Fintype.card_le_of_injective t t.injective
    simp only [Fintype.card_fin] at hcard
    omega

def affinePairTuple {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : @OrderEmbedding (Fin 2) V inferInstance order.toLE := by
  let : LinearOrder V := order
  apply OrderEmbedding.ofStrictMono (Function.Embedding.embFinTwo (ne_of_lt hxy))
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Function.Embedding.embFinTwo_apply_zero, Function.Embedding.embFinTwo_apply_one]

@[simp] theorem affinePairTuple_zero {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : affinePairTuple order x y hxy 0 = x := rfl

@[simp] theorem affinePairTuple_one {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : affinePairTuple order x y hxy 1 = y := rfl

def orderWitnessOld {V : Type v} [LinearOrder V] [Finite V] :
    @OrderEmbedding V (OrderWitnessCarrier V) inferInstance (orderWitnessOrder V).toLE :=
  @OrderEmbedding.ofStrictMono V (OrderWitnessCarrier V) inferInstance
    (orderWitnessOrder V).toPreorder Sum.inl orderWitness_old_strictMono

def pairOrderWitness {r : ℕ} {Q : Type u₁} {K : Type u₂} {P : Palette Q} {R : Palette K}
    {V : Type v} [LinearOrder V] [Finite V] (A : Pair r P R V) (q : Q) (k : K) :
    Pair r P R (OrderWitnessCarrier V) :=
  @Pair.extendOrdered r Q K P R V (OrderWitnessCarrier V) inferInstance
    (orderWitnessOrder V) A orderWitnessOld q k

def pairOrderWitness_oldEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} [LinearOrder V] [Finite V]
    (A : Pair r P R V) (q : Q) (k : K) :
    Embedding (toOrderedPair A inferInstance)
      (toOrderedPair (pairOrderWitness A q k) (orderWitnessOrder V)) :=
  @pairOrderedEmbedding r Q K P R V (OrderWitnessCarrier V) inferInstance
    (orderWitnessOrder V) A _ orderWitnessOld
      (@Pair.extendOrdered_preserves r Q K P R V (OrderWitnessCarrier V) inferInstance
        (orderWitnessOrder V) A orderWitnessOld q k)

def pairOrderWitness_left {r : ℕ} (hr : 2 ≤ r) {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} [LinearOrder V] [Finite V]
    (A : Pair r P R V) (q : Q) (k : K) (p : OrderWitness (V := V)) :
    Embedding (orderedPairEdgeModel r P R q k)
      (toOrderedPair (pairOrderWitness A q k) (orderWitnessOrder V)) := by
  let e := affinePairTuple (orderWitnessOrder V) (.inl p.1.1) (.inr p) (orderWitness_lower p)
  apply @pairOrderedEmbedding r Q K P R (Fin 2) (OrderWitnessCarrier V) inferInstance
    (orderWitnessOrder V) _ _ e
  apply @pairEdgeModel_preserves_extend r hr Q K P R V (OrderWitnessCarrier V)
    inferInstance (orderWitnessOrder V) A orderWitnessOld q k e
  refine ⟨1, ?_⟩
  rintro ⟨x, hx⟩
  change Sum.inl x = Sum.inr p at hx
  cases hx

def pairOrderWitness_right {r : ℕ} (hr : 2 ≤ r) {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} [LinearOrder V] [Finite V]
    (A : Pair r P R V) (q : Q) (k : K) (p : OrderWitness (V := V)) :
    Embedding (orderedPairEdgeModel r P R q k)
      (toOrderedPair (pairOrderWitness A q k) (orderWitnessOrder V)) := by
  let e := affinePairTuple (orderWitnessOrder V) (.inr p) (.inl p.1.2) (orderWitness_upper p)
  apply @pairOrderedEmbedding r Q K P R (Fin 2) (OrderWitnessCarrier V) inferInstance
    (orderWitnessOrder V) _ _ e
  apply @pairEdgeModel_preserves_extend r hr Q K P R V (OrderWitnessCarrier V)
    inferInstance (orderWitnessOrder V) A orderWitnessOld q k e
  refine ⟨0, ?_⟩
  rintro ⟨x, hx⟩
  change Sum.inl x = Sum.inr p at hx
  cases hx

def pairEdgeOrderColor {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {q : Q} {k : K} {V : Type v}
    {C : Structure (orderedPairLanguage r P R) V} (order : LinearOrder V)
    (e : Embedding (orderedPairEdgeModel r P R q k) C) : Bool := by
  classical
  exact decide (@LT.lt V order.toLT (e 0) (e 1))

@[simp] theorem pairEdgeOrderColor_true {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {q : Q} {k : K} {V : Type v}
    {C : Structure (orderedPairLanguage r P R) V} (order : LinearOrder V)
    (e : Embedding (orderedPairEdgeModel r P R q k) C) :
    pairEdgeOrderColor order e = true ↔ @LT.lt V order.toLT (e 0) (e 1) := by
  classical
  simp only [pairEdgeOrderColor, decide_eq_true_eq]

@[simp] theorem pairEdgeOrderColor_false {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {q : Q} {k : K} {V : Type v}
    {C : Structure (orderedPairLanguage r P R) V} (order : LinearOrder V)
    (e : Embedding (orderedPairEdgeModel r P R q k) C) :
    pairEdgeOrderColor order e = false ↔ ¬ @LT.lt V order.toLT (e 0) (e 1) := by
  classical
  simp only [pairEdgeOrderColor, decide_eq_false_iff_not]

/-- Homogeneity of one edge type forces a common order direction on the
whole original substructure, including the binary lower-arity case. -/
theorem pairOrderWitness_homogeneity {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} {P : Palette Q} {R : Palette K}
    {V : Type v} {W : Type w} [LinearOrder V] [Finite V]
    (A : Pair r P R V) (q : Q) (k : K) (B : Pair r P R W)
    (oldB newB : LinearOrder W)
    (f : Embedding (toOrderedPair (pairOrderWitness A q k) (orderWitnessOrder V))
      (toOrderedPair B oldB))
    (hhom : ∀ e₁ e₂ : Embedding (orderedPairEdgeModel r P R q k)
        (toOrderedPair (pairOrderWitness A q k) (orderWitnessOrder V)),
      pairEdgeOrderColor newB (f.comp e₁) = pairEdgeOrderColor newB (f.comp e₂)) :
    (@StrictMono V W inferInstance newB.toPreorder (fun x => f (.inl x))) ∨
      (@StrictAnti V W inferInstance newB.toPreorder (fun x => f (.inl x))) := by
  classical
  let : LinearOrder W := newB
  by_cases hp : ∃ x y : V, x < y
  · obtain ⟨x, y, hxy⟩ := hp
    let p₀ : OrderWitness (V := V) := ⟨(x, y), hxy⟩
    let baseline := pairOrderWitness_left hr A q k p₀
    cases hc : pairEdgeOrderColor newB (f.comp baseline) with
    | false =>
      right
      intro a b hab
      let p : OrderWitness (V := V) := ⟨(a, b), hab⟩
      have hleft := (hhom (pairOrderWitness_left hr A q k p) baseline).trans hc
      have hright := (hhom (pairOrderWitness_right hr A q k p) baseline).trans hc
      have hnotL := (pairEdgeOrderColor_false newB _).mp hleft
      have hnotR := (pairEdgeOrderColor_false newB _).mp hright
      change ¬ f (.inl a) < f (.inr p) at hnotL
      change ¬ f (.inr p) < f (.inl b) at hnotR
      have hL : f (.inr p) < f (.inl a) := lt_of_le_of_ne (le_of_not_gt hnotL) (by
        intro he
        have hh := f.injective he
        cases hh)
      have hR : f (.inl b) < f (.inr p) := lt_of_le_of_ne (le_of_not_gt hnotR) (by
        intro he
        have hh := f.injective he
        cases hh)
      exact lt_trans hR hL
    | true =>
      left
      intro a b hab
      let p : OrderWitness (V := V) := ⟨(a, b), hab⟩
      have hleft := (hhom (pairOrderWitness_left hr A q k p) baseline).trans hc
      have hright := (hhom (pairOrderWitness_right hr A q k p) baseline).trans hc
      have hL := (pairEdgeOrderColor_true newB _).mp hleft
      have hR := (pairEdgeOrderColor_true newB _).mp hright
      change f (.inl a) < f (.inr p) at hL
      change f (.inr p) < f (.inl b) at hR
      exact lt_trans hL hR
  · left
    intro x y hxy
    exact (hp ⟨x, y, hxy⟩).elim

end

end Hypertournaments.Affine
