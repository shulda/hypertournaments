import Hypertournaments.RelationalEncoding
import Hypertournaments.Automorphism
import Hypertournaments.PartialHyper
import Mathlib.ModelTheory.Fraisse

/-!
# The first-order language of intrinsic hypertournaments

The language has exactly one relation, of arity `n`. Its interpretation is the
existing orientation-zero relation. The first-order embeddings are therefore
exactly the intrinsic orientation-preserving injections.
-/

open FirstOrder
open FirstOrder.Language

namespace Hypertournaments

universe u v

namespace Hyper

/-- Intrinsic isomorphism, without an auxiliary order or presentation. -/
def Isomorphic {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) : Prop :=
  ∃ e : V ≃ W, Preserves A B e.toEmbedding

theorem preserves_symm {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} {B : Hyper n W} {e : V ≃ W}
    (h : Preserves A B e.toEmbedding) : Preserves B A e.symm.toEmbedding := by
  intro t
  have ht : (t.trans e.symm.toEmbedding).trans e.toEmbedding = t := by
    ext x
    exact e.apply_symm_apply (t x)
  have hp := h (t.trans e.symm.toEmbedding)
  rw [ht] at hp
  exact hp.symm

/-- The unique symbol in the language of `n`-hypertournaments. -/
inductive RelationSymbol (n : ℕ) : ℕ → Type
  | edge : RelationSymbol n n

/-- A single `n`-ary relation and no function symbols. -/
def language (n : ℕ) : FirstOrder.Language where
  Functions _ := Empty
  Relations := RelationSymbol n

instance (n : ℕ) : (language n).IsRelational := by
  intro k
  change IsEmpty Empty
  infer_instance

instance (n : ℕ) : Countable (Σ k, (language n).Functions k) := by
  change Countable (Σ _ : ℕ, Empty)
  infer_instance

/-- Encode an intrinsic hypertournament as a relational structure. -/
@[instance_reducible] def foStructure {n : ℕ} {V : Type u} (A : Hyper n V) :
    (language n).Structure V where
  funMap r := Empty.elim r
  RelMap r t := by
    cases r
    exact A.Relation t

/-- First-order embeddings between the canonical encodings. -/
abbrev FOEmbedding {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) :=
  @FirstOrder.Language.Embedding (language n) V W A.foStructure B.foStructure

/-- First-order equivalences between the canonical encodings. -/
abbrev FOEquiv {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) :=
  @FirstOrder.Language.Equiv (language n) V W A.foStructure B.foStructure

/-- Preserve orientations, hence preserve and reflect the single relation. -/
def toFOEmbedding {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} {B : Hyper n W} (e : V ↪ W) (h : Preserves A B e) :
    A.FOEmbedding B := by
  let := A.foStructure
  let := B.foStructure
  exact {
    toEmbedding := e
    map_fun' := fun r => Empty.elim r
    map_rel' := by
      intro k r t
      cases r
      exact (preserves_iff_relation A B e).mp h t }

theorem preserves_of_foEmbedding {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} {B : Hyper n W} (e : A.FOEmbedding B) :
    Preserves A B (@FirstOrder.Language.Embedding.toEmbedding
      (language n) V W A.foStructure B.foStructure e) := by
  let := A.foStructure
  let := B.foStructure
  apply (preserves_iff_relation A B e.toEmbedding).mpr
  intro t
  exact e.map_rel (RelationSymbol.edge (n := n)) t

/-- A relational automorphism is an automorphism of the intrinsic orientation. -/
def autOfFOEquiv {n : ℕ} {V : Type u} {A : Hyper n V}
    (g : A.FOEquiv A) : A.Aut := by
  let := A.foStructure
  exact ⟨g.toEquiv, preserves_of_foEmbedding g.toEmbedding⟩

/-- Finite partial isomorphisms extend to actual intrinsic automorphisms. -/
def Homogeneous {n : ℕ} {V : Type u} (A : Hyper n V) : Prop :=
  ∀ (m : ℕ) (B : Hyper n (Fin m)) (f g : Fin m ↪ V),
    Preserves B A f → Preserves B A g →
      ∃ σ : A.Aut, ∀ x, (σ : Equiv.Perm V) (f x) = g x

/-- Native first-order ultrahomogeneity implies intrinsic homogeneity. -/
theorem homogeneous_of_isUltrahomogeneous {n : ℕ} {V : Type u}
    (A : Hyper n V)
    (h : @FirstOrder.Language.IsUltrahomogeneous (language n) V A.foStructure) :
    A.Homogeneous := by
  let := A.foStructure
  intro m B f g hf hg
  let := B.foStructure
  let F : Fin m ↪[language n] V := toFOEmbedding f hf
  let G : Fin m ↪[language n] V := toFOEmbedding g hg
  have hfg : FirstOrder.Language.Structure.FG (language n) (Fin m) :=
    FirstOrder.Language.Structure.fg_iff_finite.mpr inferInstance
  obtain ⟨σ, hσ⟩ := h F.toHom.range (hfg.range F.toHom)
    (G.comp F.equivRange.symm.toEmbedding)
  refine ⟨autOfFOEquiv σ, ?_⟩
  intro x
  have hx := congrArg (fun e : F.toHom.range ↪[language n] V =>
    e (F.equivRange x)) hσ
  change G (F.equivRange.symm (F.equivRange x)) = σ (F x) at hx
  rw [FirstOrder.Language.Equiv.symm_apply_apply] at hx
  exact hx.symm

/-- On a finite carrier only finitely many orientation tables exist. -/
instance finite {n : ℕ} {V : Type u} [Finite V] : Finite (Hyper n V) := by
  apply Finite.of_injective (fun A : Hyper n V => A.orient)
  intro A B h
  cases A
  cases B
  cases h
  rfl

end Hyper

/-- An embedding into a forbidden-free hypertournament has forbidden-free source. -/
theorem omits_of_preserves {n : ℕ} {V W : Type*}
    {family : ForbiddenFamily n} {A : Hyper n V} {B : Hyper n W}
    {e : V ↪ W} (he : Preserves A B e) (hB : Omits family B) :
    Omits family A := by
  intro m F hF f hf
  apply hB m F hF (f.trans e)
  intro t
  exact (he (t.trans f)).trans (hf t)

end Hypertournaments
