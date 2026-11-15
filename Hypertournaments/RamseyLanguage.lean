import Hypertournaments.RelationalEncoding
import Hypertournaments.PartialHyper
import PartiteConstruction.Structure.Order
import PartiteConstruction.Functional.SingletonExpansion

/-!
# Native relational language for the hypertournament Ramsey construction

There is one n-ary relation and no function symbols. Relation truth means
orientation false, including the exclusion of repeated coordinates. Arbitrary
partial native structures remain arbitrary structures in this same language.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey

/-- The unordered orientation language, with no functions. -/
def orientationLanguage (n : ℕ) : Language where
  RelSymbol := Unit
  FuncSymbol := Empty
  relArity _ := n
  funcArity F := nomatch F

abbrev orderedLanguage (n : ℕ) := (orientationLanguage n).withLinearOrder

instance orientationLanguage_isEmptyFuncSymbol (n : ℕ) :
    IsEmpty (orientationLanguage n).FuncSymbol := by
  change IsEmpty Empty
  infer_instance

instance orderedLanguage_isEmptyFuncSymbol (n : ℕ) :
    IsEmpty (orderedLanguage n).FuncSymbol := by
  change IsEmpty Empty
  infer_instance

/-- The native relational presentation of the shared intrinsic Hyper. -/
def toNative {n : ℕ} {V : Type v} (A : Hyper n V) : Structure (orientationLanguage n) V where
  rel _ t := A.Relation t
  func F := nomatch F

/-- A freely ordered expansion on the same carrier. -/
def toOrderedNative {n : ℕ} {V : Type v} (A : Hyper n V) (order : LinearOrder V) :
    Structure (orderedLanguage n) V :=
  @Structure.withLinearOrder (orientationLanguage n) V (toNative A) order.toLT

@[simp] theorem toNative_rel {n : ℕ} {V : Type v} (A : Hyper n V) (t : Fin n → V) :
    (toNative A).rel () t ↔ A.Relation t := Iff.rfl

@[simp] theorem toOrderedNative_rel {n : ℕ} {V : Type v}
    (A : Hyper n V) (order : LinearOrder V) (t : Fin n → V) :
    (toOrderedNative A order).rel (.inl ()) t ↔ A.Relation t := Iff.rfl

@[simp] theorem toOrderedNative_lt {n : ℕ} {V : Type v}
    (A : Hyper n V) (order : LinearOrder V) (t : Fin 2 → V) :
    (toOrderedNative A order).rel (.inr ()) t ↔ @LT.lt V order.toLT (t 0) (t 1) := Iff.rfl

/-- Every subset is closed in this purely relational language. -/
theorem isClosed {n : ℕ} {V : Type v}
    (C : Structure (orderedLanguage n) V) (S : Set V) : C.IsClosed S := by
  intro F
  exact nomatch F

theorem singletonValued {n : ℕ} {V : Type v}
    (C : Structure (orderedLanguage n) V) : C.SingletonValued := by
  intro F
  exact nomatch F

/-- The two relational fields determine a native structure in our language. -/
theorem native_ext {n : ℕ} {V : Type v}
    {C D : Structure (orderedLanguage n) V}
    (h : ∀ R t, C.rel R t ↔ D.rel R t) : C = D := by
  cases C with | mk cr cf =>
    cases D with | mk dr df =>
      have hr : cr = dr := funext fun R => funext fun t => propext (h R t)
      have hf : cf = df := funext fun F => nomatch F
      cases hr
      cases hf
      rfl

/-- Native embeddings are exactly the original intrinsic embeddings, before ordering. -/
def nativeEmbedding {n : ℕ} {V : Type v} {W : Type w}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) (he : Preserves A B e) :
    Structure.Embedding (toNative A) (toNative B) where
  toFun := e
  injective := e.injective
  map_rel_iff _ t := (preserves_iff_relation A B e).mp he t
  map_func F := nomatch F

theorem preserves_of_nativeEmbedding {n : ℕ} {V : Type v} {W : Type w}
    (A : Hyper n V) (B : Hyper n W) (e : Structure.Embedding (toNative A) (toNative B)) :
    Preserves A B e.toFunctionEmbedding := by
  apply (preserves_iff_relation A B e.toFunctionEmbedding).mpr
  intro t
  exact e.map_rel_iff () t

/-- Adding compatible orders gives a full native embedding, including reflection. -/
def orderedEmbedding {n : ℕ} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W]
    (A : Hyper n V) (B : Hyper n W) (e : V ↪o W)
    (he : Preserves A B e.toEmbedding) :
    Structure.Embedding (toOrderedNative A inferInstance) (toOrderedNative B inferInstance) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    cases R with
    | inl R => exact (preserves_iff_relation A B e.toEmbedding).mp he t
    | inr R => exact e.lt_iff_lt
  map_func F := nomatch F

theorem preserves_of_orderedEmbedding {n : ℕ} {V : Type v} {W : Type w}
    (A : Hyper n V) (B : Hyper n W) (oV : LinearOrder V) (oW : LinearOrder W)
    (e : Structure.Embedding (toOrderedNative A oV) (toOrderedNative B oW)) :
    Preserves A B e.toFunctionEmbedding := by
  apply (preserves_iff_relation A B e.toFunctionEmbedding).mpr
  intro t
  exact e.map_rel_iff (.inl ()) t

theorem strictMono_of_orderedEmbedding {n : ℕ} {V : Type v} {W : Type w}
    [LinearOrder V] [LinearOrder W] (A : Hyper n V) (B : Hyper n W)
    (e : Structure.Embedding (toOrderedNative A inferInstance) (toOrderedNative B inferInstance)) :
    StrictMono e := e.strictMono

/-- Class membership includes finiteness on the entire native carrier. -/
def orderedOmissionClass {n : ℕ} (family : ForbiddenFamily n)
    {V : Type v} (C : Structure (orderedLanguage n) V) : Prop :=
  Finite V ∧ ∃ (A : Hyper n V) (order : LinearOrder V),
    Omits family A ∧ C = toOrderedNative A order

end Hypertournaments.Ramsey
