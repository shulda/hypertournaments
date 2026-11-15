import Hypertournaments.Affine.PairLanguage
import Hypertournaments.Affine.OrderedLabels
import CCO.UnaryHN.OrderedAmbient
import Mathlib.Tactic.Ext

/-!
# Ramsey for freely ordered independent labelled structures

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the affine potential construction. The pinned ambient Ramsey theorem is
applied to the full native encoding. An arbitrary relational witness is
decoded by reading its unique colour on each increasing tuple when one
exists, and using a fixed fallback otherwise. Every fully encoded copy
survives this decoding with its actual vertex map unchanged.
-/

universe u₁ u₂ v w z

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

noncomputable section

/-- Read the unique satisfied label, with an explicit fallback for arbitrary inputs. -/
def uniqueLabel {Q : Type u₁} (rel : Q → Prop) (fallback : Q) : Q := by
  classical
  exact if h : ∃! q, rel q then h.choose else fallback

theorem uniqueLabel_eq {Q : Type u₁} (rel : Q → Prop) (fallback value : Q)
    (h : ∀ q, rel q ↔ value = q) : uniqueLabel rel fallback = value := by
  classical
  have hu : ∃! q, rel q :=
    ⟨value, (h value).mpr rfl, fun q hq => ((h q).mp hq).symm⟩
  unfold uniqueLabel
  rw [dite_eq_left hu]
  exact ((h _).mp hu.choose_spec.1).symm

/-- Only actual subsets of the specified arity are used in the decoder. -/
def decodedLabelTable {n : ℕ} {Q : Type u₁} {X : Type v} [LinearOrder X]
    (rel : Q → (Fin n → X) → Prop) (fallback : Q) (S : Finset X) : Q :=
  if hS : S.card = n then uniqueLabel (fun q => rel q (S.orderEmbOfFin hS)) fallback
    else fallback

def decodeLabelled {n : ℕ} {Q : Type u₁} (P : Palette Q)
    {X : Type v} [LinearOrder X] (rel : Q → (Fin n → X) → Prop) (fallback : Q) :
    Labelled n P X := Labelled.fromOrderedLabels P (decodedLabelTable rel fallback)

/-- An increasing tuple reads the label selector on that literal tuple. -/
theorem decodeLabelled_label_strictMono {n : ℕ} {Q : Type u₁} (P : Palette Q)
    {X : Type v} [LinearOrder X] (rel : Q → (Fin n → X) → Prop) (fallback : Q)
    (t : Fin n ↪ X) (ht : StrictMono (t : Fin n → X)) :
    (decodeLabelled P rel fallback).label t = uniqueLabel (fun q => rel q t) fallback := by
  rw [decodeLabelled, fromOrderedLabels_label_strictMono P _ t ht]
  let S := tupleVertices t
  have hS : S.card = n := by
    dsimp [S, tupleVertices]
    rw [Finset.card_image_of_injective _ t.injective]
    simp
  have hcanonical : (t : Fin n → X) = S.orderEmbOfFin hS :=
    Finset.orderEmbOfFin_unique hS
      (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)) ht
  change decodedLabelTable rel fallback S = _
  rw [decodedLabelTable, dite_eq_left hS]
  exact congrArg (fun f : Fin n → X => uniqueLabel (fun q => rel q f) fallback)
    hcanonical.symm

/-- Every fully encoded source copy is preserved by canonical decoding.
The relation premise includes reflection and tuples with repeated coordinates. -/
theorem decodeLabelled_preserves {n : ℕ} {Q : Type u₁} {P : Palette Q}
    {V : Type v} {X : Type w} [LinearOrder V] [LinearOrder X]
    (A : Labelled n P V) (rel : Q → (Fin n → X) → Prop) (fallback : Q)
    (e : V ↪o X)
    (hrel : ∀ q (t : Fin n → V), rel q (e ∘ t) ↔ A.Relation q t) :
    A.Preserves (decodeLabelled P rel fallback) e.toEmbedding := by
  apply A.preserves_of_canonical
  intro S hS
  let t := (S.orderEmbOfFin hS).toEmbedding
  have ht : StrictMono (t : Fin n → V) := (S.orderEmbOfFin hS).strictMono
  rw [decodeLabelled_label_strictMono P rel fallback (t.trans e.toEmbedding)
    (e.strictMono.comp ht)]
  apply uniqueLabel_eq
  intro q
  exact (hrel q t).trans (A.relation_embedding q t)

/-- Decode both arities of an arbitrary native relational structure. -/
def decodePair {r : ℕ} {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) {X : Type v}
    (C : Structure (pairLanguage r P R) X) (order : LinearOrder X)
    (fallbackQ : Q) (fallbackK : K) : Pair r P R X where
  low := @decodeLabelled r Q P X order (fun q => C.rel (.inl q)) fallbackQ
  high := @decodeLabelled (r + 1) K R X order (fun k => C.rel (.inr k)) fallbackK

/-- The encoded ordered models satisfy the ambient theorem's input class. -/
theorem toOrderedPair_mem_allOrderedModels {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v}
    (A : Pair r P R V) (order : LinearOrder V) :
    CCO.UnaryHN.Native.AllOrderedModels (pairLanguage r P R) (toOrderedPair A order) := by
  refine ⟨toPairNative A, order, ?_, rfl⟩
  intro F
  exact nomatch F

/-- Decoding preserves any full encoded copy, with the same underlying map. -/
def decodedPairEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {X : Type w}
    (A : Pair r P R V) (orderA : LinearOrder V)
    (C : Structure (pairLanguage r P R) X) (orderX : LinearOrder X)
    (fallbackQ : Q) (fallbackK : K)
    (e : Embedding (toOrderedPair A orderA)
      (@Structure.withLinearOrder (pairLanguage r P R) X C orderX.toLT)) :
    Embedding (toOrderedPair A orderA)
      (toOrderedPair (decodePair P R C orderX fallbackQ fallbackK) orderX) := by
  let : LinearOrder V := orderA
  let : LinearOrder X := orderX
  let eo : V ↪o X := OrderEmbedding.ofStrictMono e e.strictMono
  apply pairOrderedEmbedding A _ eo
  constructor
  · apply decodeLabelled_preserves A.low (fun q => C.rel (.inl q)) fallbackQ eo
    intro q t
    exact e.map_rel_iff (.inl (.inl q)) t
  · apply decodeLabelled_preserves A.high (fun k => C.rel (.inr k)) fallbackK eo
    intro k t
    exact e.map_rel_iff (.inl (.inr k)) t

@[simp] theorem decodedPairEmbedding_apply {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {X : Type w}
    (A : Pair r P R V) (orderA : LinearOrder V)
    (C : Structure (pairLanguage r P R) X) (orderX : LinearOrder X)
    (fallbackQ : Q) (fallbackK : K)
    (e : Embedding (toOrderedPair A orderA)
      (@Structure.withLinearOrder (pairLanguage r P R) X C orderX.toLT)) (x : V) :
    decodedPairEmbedding A orderA C orderX fallbackQ fallbackK e x = e x := rfl

/-- Actual finite ordered pair witnesses for every arity and finite nonempty
colour palette. Finiteness of the two label palettes is not needed here. -/
theorem exists_pair_ordered_ramsey_witness (r : ℕ) {Q : Type u₁} {K : Type u₂}
    [Nonempty Q] [Nonempty K] (P : Palette Q) (R : Palette K)
    {V W : Type v} [Finite V] [Finite W]
    (A : Pair r P R V) (B : Pair r P R W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (κ : Type z) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Pair r P R X) (order : LinearOrder X),
      Structure.Arrow (toOrderedPair A orderA) (toOrderedPair B orderB)
        (toOrderedPair D order) κ := by
  classical
  obtain ⟨X, hX, C, hC, arrow⟩ :=
    CCO.UnaryHN.Native.allOrderedModels_ramsey (pairLanguage r P R)
      (toOrderedPair A orderA) (toOrderedPair B orderB)
      (toOrderedPair_mem_allOrderedModels A orderA)
      (toOrderedPair_mem_allOrderedModels B orderB) κ
  rcases hC with ⟨old, order, _hold, rfl⟩
  let fallbackQ : Q := Classical.choice inferInstance
  let fallbackK : K := Classical.choice inferInstance
  let D := decodePair P R old order fallbackQ fallbackK
  refine ⟨X, hX, D, order, ?_⟩
  intro χ
  let χ' : Embedding (toOrderedPair A orderA)
      (@Structure.withLinearOrder (pairLanguage r P R) X old order.toLT) → κ :=
    fun e => χ (decodedPairEmbedding A orderA old order fallbackQ fallbackK e)
  obtain ⟨f, hf⟩ := arrow χ'
  refine ⟨decodedPairEmbedding B orderB old order fallbackQ fallbackK f, ?_⟩
  intro e₁ e₂
  have he (e : Embedding (toOrderedPair A orderA) (toOrderedPair B orderB)) :
      decodedPairEmbedding A orderA old order fallbackQ fallbackK (f.comp e) =
        (decodedPairEmbedding B orderB old order fallbackQ fallbackK f).comp e := by
    ext x
    rfl
  simpa only [χ', he] using hf e₁ e₂

/-- The full native class of freely ordered independent label structures is Ramsey. -/
theorem pair_ordered_ramsey (r : ℕ) {Q : Type u₁} {K : Type u₂}
    [Nonempty Q] [Nonempty K] (P : Palette Q) (R : Palette K) :
    CCO.UnaryHN.Native.Ramsey.{max u₁ u₂,v,z}
      (orderedPairClass (r := r) (P := P) (R := R)) := by
  intro V W _ _ A B hA hB κ _ _
  rcases hA with ⟨hV, AA, orderA, rfl⟩
  rcases hB with ⟨hW, BB, orderB, rfl⟩
  let : Finite V := hV
  let : Finite W := hW
  obtain ⟨X, hX, D, order, arrow⟩ :=
    exists_pair_ordered_ramsey_witness r P R AA BB orderA orderB κ
  exact ⟨X, hX, toOrderedPair D order, ⟨hX, D, order, rfl⟩, arrow⟩

end

end Hypertournaments.Affine
