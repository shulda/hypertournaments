import Hypertournaments.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ext

/-!
# Intrinsic structures labelled by an involutive palette

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the final subsection, `Further potential constructions`.
No finiteness, nonemptiness or fixed-point-freeness of the palette is assumed.
-/

namespace Hypertournaments.Affine

universe u v w

/-- Labels change by a specified involution under odd coordinate permutations. -/
structure Palette (Q : Type u) where
  star : Q → Q
  involutive_star : Function.Involutive star

@[simp] theorem Palette.star_star {Q : Type u} (P : Palette Q) (q : Q) :
    P.star (P.star q) = q := P.involutive_star q

theorem Palette.star_injective {Q : Type u} (P : Palette Q) :
    Function.Injective P.star := P.involutive_star.injective

/-- The affine involution on an abelian group. -/
def Palette.affine {G : Type u} [AddCommGroup G] (a : G) : Palette G where
  star g := a - g
  involutive_star g := sub_sub_cancel a g

@[simp] theorem Palette.affine_star {G : Type u} [AddCommGroup G] (a g : G) :
    (Palette.affine a).star g = a - g := rfl

/-- A freely paired palette, retaining the colour and reversing its Boolean sheet. -/
def Palette.free (K : Type u) : Palette (K × Bool) where
  star q := (q.1, !q.2)
  involutive_star q := by cases q with | mk k b => cases b <;> rfl

@[simp] theorem Palette.free_star {K : Type u} (q : K × Bool) :
    (Palette.free K).star q = (q.1, !q.2) := rfl

/-- A palette all of whose labels are fixed by the involution. -/
def Palette.trivial (Q : Type u) : Palette Q where
  star := id
  involutive_star _ := rfl

@[simp] theorem Palette.trivial_star {Q : Type u} (q : Q) :
    (Palette.trivial Q).star q = q := rfl

/-- An intrinsic involution-labelled structure on actual injective tuples. -/
structure Labelled (n : ℕ) {Q : Type u} (P : Palette Q) (V : Type v) where
  label : (Fin n ↪ V) → Q
  swap_label : ∀ (f : Fin n ↪ V) (i j : Fin n), i ≠ j →
    label ((Equiv.swap i j).toEmbedding.trans f) = P.star (label f)

@[ext] theorem Labelled.ext {n : ℕ} {Q : Type u} {P : Palette Q} {V : Type v}
    {A B : Labelled n P V} (h : ∀ t, A.label t = B.label t) : A = B := by
  cases A with
  | mk a ha =>
    cases B with
    | mk b hb =>
      have hab : a = b := funext h
      cases hab
      rfl

/-- Vertex injections preserve every tuple label. -/
def Labelled.Preserves {n : ℕ} {Q : Type u} {P : Palette Q} {V : Type v} {W : Type w}
    (A : Labelled n P V) (B : Labelled n P W) (e : V ↪ W) : Prop :=
  ∀ t : Fin n ↪ V, B.label (t.trans e) = A.label t

theorem Labelled.Preserves.refl {n : ℕ} {Q : Type u} {P : Palette Q} {V : Type v}
    (A : Labelled n P V) : A.Preserves A (Function.Embedding.refl V) := fun _ => rfl

theorem Labelled.Preserves.comp {n : ℕ} {Q : Type u} {P : Palette Q}
    {U : Type v} {V : Type w} {W : Type*}
    {A : Labelled n P U} {B : Labelled n P V} {C : Labelled n P W}
    {e : U ↪ V} {f : V ↪ W} (he : A.Preserves B e) (hf : B.Preserves C f) :
    A.Preserves C (e.trans f) := fun t => (hf (t.trans e)).trans (he t)

/-- Intrinsic pullback of the complete labelled structure. -/
def Labelled.pullback {n : ℕ} {Q : Type u} {P : Palette Q} {V : Type v} {W : Type w}
    (B : Labelled n P W) (e : V ↪ W) : Labelled n P V where
  label t := B.label (t.trans e)
  swap_label t i j hij := B.swap_label (t.trans e) i j hij

theorem Labelled.preserves_pullback {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} {W : Type w} (B : Labelled n P W) (e : V ↪ W) :
    (B.pullback e).Preserves B e := fun _ => rfl

/-- The full permutation law follows solely from the palette involution. -/
theorem Labelled.label_perm {n : ℕ} {Q : Type u} {P : Palette Q} {V : Type v}
    (A : Labelled n P V) (t : Fin n ↪ V) (σ : Equiv.Perm (Fin n)) :
    A.label (σ.toEmbedding.trans t) =
      if σ.sign = (1 : ℤˣ) then A.label t else P.star (A.label t) := by
  refine Equiv.Perm.swap_induction_on' σ ?_ ?_
  · have h : ((1 : Equiv.Perm (Fin n)).toEmbedding.trans t) = t := by
      ext i
      rfl
    simp [h]
  · intro τ i j hij ih
    have hswap := A.swap_label (τ.toEmbedding.trans t) i j hij
    have hcomp :
        ((τ * Equiv.swap i j).toEmbedding.trans t) =
          (Equiv.swap i j).toEmbedding.trans (τ.toEmbedding.trans t) := by
      ext x
      rfl
    rw [hcomp, hswap, ih, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    rcases Int.units_eq_one_or τ.sign with h | h <;> simp [h, Units.ext_iff]

instance Labelled.finite {n : ℕ} {Q : Type u} [Finite Q] {P : Palette Q}
    {V : Type v} [Finite V] : Finite (Labelled n P V) := by
  let : Finite (Fin n ↪ V) := Finite.of_injective
    (fun e : Fin n ↪ V => (e : Fin n → V))
    (fun _ _ h => Function.Embedding.ext (congrFun h))
  exact Finite.of_injective (fun A : Labelled n P V => A.label)
    (fun _ _ h => Labelled.ext (congrFun h))

end Hypertournaments.Affine
