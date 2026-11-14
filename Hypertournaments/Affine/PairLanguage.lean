import Hypertournaments.Affine.Basic
import PartiteConstruction.Structure.Order
import Mathlib.Tactic.Ext

/-!
# The native language for two independent involutive label structures

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the affine potential construction. Both arities and every actual label are
named. Repeated tuples satisfy no label relation; native embeddings preserve
and reflect the labels on all injective tuples and the auxiliary free order.
-/

universe u₁ u₂ v w z

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

/-- Two consecutive label arities on one carrier, with no compatibility equation. -/
structure Pair (r : ℕ) {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) (V : Type v) where
  low : Labelled r P V
  high : Labelled (r + 1) R V

namespace Pair

variable {r : ℕ} {Q : Type u₁} {K : Type u₂} {P : Palette Q} {R : Palette K}
  {V : Type v} {W : Type w} {X : Type z}

/-- The original vertex injection preserves both independent label structures. -/
def Preserves (A : Pair r P R V) (B : Pair r P R W) (e : V ↪ W) : Prop :=
  A.low.Preserves B.low e ∧ A.high.Preserves B.high e

def pullback (B : Pair r P R W) (e : V ↪ W) : Pair r P R V where
  low := B.low.pullback e
  high := B.high.pullback e

@[ext] theorem ext {A B : Pair r P R V} (hlow : A.low = B.low)
    (hhigh : A.high = B.high) : A = B := by
  cases A
  cases B
  cases hlow
  cases hhigh
  rfl

instance [Finite Q] [Finite K] [Finite V] : Finite (Pair r P R V) :=
  Finite.of_injective (fun A : Pair r P R V => (A.low, A.high))
    (fun _ _ h => ext (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem preserves_refl (A : Pair r P R V) :
    A.Preserves A (Function.Embedding.refl V) := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Preserves.comp {A : Pair r P R V} {B : Pair r P R W}
    {C : Pair r P R X} {e : V ↪ W} {f : W ↪ X}
    (hAB : A.Preserves B e) (hBC : B.Preserves C f) :
    A.Preserves C (e.trans f) :=
  ⟨fun t => (hBC.1 (t.trans e)).trans (hAB.1 t),
    fun t => (hBC.2 (t.trans e)).trans (hAB.2 t)⟩

theorem preserves_pullback (B : Pair r P R W) (e : V ↪ W) :
    (B.pullback e).Preserves B e := ⟨fun _ => rfl, fun _ => rfl⟩

end Pair

/-- A named label relation, false on every tuple with a repeated coordinate. -/
def Labelled.Relation {n : ℕ} {Q : Type u₁} {P : Palette Q} {V : Type v}
    (A : Labelled n P V) (q : Q) (t : Fin n → V) : Prop :=
  ∃ h : Function.Injective t, A.label ⟨t, h⟩ = q

@[simp] theorem Labelled.relation_embedding {n : ℕ} {Q : Type u₁}
    {P : Palette Q} {V : Type v} (A : Labelled n P V) (q : Q) (t : Fin n ↪ V) :
    A.Relation q t ↔ A.label t = q := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨t.injective, h⟩

theorem Labelled.preserves_iff_relation {n : ℕ} {Q : Type u₁} {P : Palette Q}
    {V : Type v} {W : Type w} (A : Labelled n P V) (B : Labelled n P W) (e : V ↪ W) :
    A.Preserves B e ↔ ∀ (q : Q) (t : Fin n → V),
      B.Relation q (e ∘ t) ↔ A.Relation q t := by
  constructor
  · intro he q t
    constructor
    · rintro ⟨ht, hb⟩
      have hinj : Function.Injective t := fun _ _ hxy => ht (congrArg e hxy)
      exact ⟨hinj, (he ⟨t, hinj⟩).symm.trans hb⟩
    · rintro ⟨ht, ha⟩
      exact ⟨e.injective.comp ht, (he ⟨t, ht⟩).trans ha⟩
  · intro h t
    have hh := (h (A.label t) (t : Fin n → V)).mpr ⟨t.injective, rfl⟩
    exact hh.choose_spec

/-- One relation for each lower and upper label; the language has no functions. -/
def pairLanguage (r : ℕ) {Q : Type u₁} {K : Type u₂}
    (_P : Palette Q) (_R : Palette K) : Language.{max u₁ u₂} where
  RelSymbol := Q ⊕ K
  FuncSymbol := PEmpty.{max u₁ u₂ + 1}
  relArity | .inl _ => r | .inr _ => r + 1
  funcArity F := nomatch F

abbrev orderedPairLanguage (r : ℕ) {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) := (pairLanguage r P R).withLinearOrder

def toPairNative {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} (A : Pair r P R V) :
    Structure (pairLanguage r P R) V where
  rel | .inl q, t => A.low.Relation q t | .inr k, t => A.high.Relation k t
  func F := nomatch F

/-- The two independent label structures together with one free linear order. -/
def toOrderedPair {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v}
    (A : Pair r P R V) (order : LinearOrder V) : Structure (orderedPairLanguage r P R) V :=
  @Structure.withLinearOrder (pairLanguage r P R) V (toPairNative A) order.toLT

@[simp] theorem toOrderedPair_low_rel {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} (A : Pair r P R V)
    (order : LinearOrder V) (q : Q) (t : Fin r → V) :
    (toOrderedPair A order).rel (.inl (.inl q)) t ↔ A.low.Relation q t := Iff.rfl

@[simp] theorem toOrderedPair_high_rel {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} (A : Pair r P R V)
    (order : LinearOrder V) (k : K) (t : Fin (r + 1) → V) :
    (toOrderedPair A order).rel (.inl (.inr k)) t ↔ A.high.Relation k t := Iff.rfl

@[simp] theorem toOrderedPair_lt {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} (A : Pair r P R V)
    (order : LinearOrder V) (t : Fin 2 → V) :
    (toOrderedPair A order).rel (.inr ()) t ↔
      @LT.lt V order.toLT (t 0) (t 1) := Iff.rfl

def pairNativeEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    (A : Pair r P R V) (B : Pair r P R W) (e : V ↪ W)
    (he : A.Preserves B e) : Embedding (toPairNative A) (toPairNative B) where
  toFun := e
  injective := e.injective
  map_rel_iff s t := by
    cases s with
    | inl q => exact (A.low.preserves_iff_relation B.low e).mp he.1 q t
    | inr k => exact (A.high.preserves_iff_relation B.high e).mp he.2 k t
  map_func F := nomatch F

theorem preserves_of_pairNativeEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    (A : Pair r P R V) (B : Pair r P R W)
    (e : Embedding (toPairNative A) (toPairNative B)) :
    A.Preserves B e.toFunctionEmbedding := by
  constructor
  · apply (A.low.preserves_iff_relation B.low e.toFunctionEmbedding).mpr
    intro q t
    exact e.map_rel_iff (.inl q) t
  · apply (A.high.preserves_iff_relation B.high e.toFunctionEmbedding).mpr
    intro k t
    exact e.map_rel_iff (.inr k) t

/-- Both named label relations and the order are preserved and reflected. -/
def pairOrderedEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W] (A : Pair r P R V) (B : Pair r P R W)
    (e : V ↪o W) (he : A.Preserves B e.toEmbedding) :
    Embedding (toOrderedPair A inferInstance) (toOrderedPair B inferInstance) where
  toFun := e
  injective := e.injective
  map_rel_iff S t := by
    rcases S with s | _
    · cases s with
      | inl q => exact (A.low.preserves_iff_relation B.low e.toEmbedding).mp he.1 q t
      | inr k => exact (A.high.preserves_iff_relation B.high e.toEmbedding).mp he.2 k t
    · exact e.lt_iff_lt
  map_func F := nomatch F

theorem preserves_of_pairOrderedEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    (A : Pair r P R V) (B : Pair r P R W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedPair A orderA) (toOrderedPair B orderB)) :
    A.Preserves B e.toFunctionEmbedding := by
  constructor
  · apply (A.low.preserves_iff_relation B.low e.toFunctionEmbedding).mpr
    intro q t
    exact e.map_rel_iff (.inl (.inl q)) t
  · apply (A.high.preserves_iff_relation B.high e.toFunctionEmbedding).mpr
    intro k t
    exact e.map_rel_iff (.inl (.inr k)) t

theorem strictMono_of_pairOrderedEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W] (A : Pair r P R V) (B : Pair r P R W)
    (e : Embedding (toOrderedPair A inferInstance) (toOrderedPair B inferInstance)) :
    StrictMono e := e.strictMono

/-- The full native ordered class, including finiteness of its actual carrier. -/
def orderedPairClass {r : ℕ} {Q : Type u₁} {K : Type u₂} {P : Palette Q} {R : Palette K}
    {V : Type v} (C : Structure (orderedPairLanguage r P R) V) : Prop :=
  Finite V ∧ ∃ (A : Pair r P R V) (order : LinearOrder V), C = toOrderedPair A order

end Hypertournaments.Affine
