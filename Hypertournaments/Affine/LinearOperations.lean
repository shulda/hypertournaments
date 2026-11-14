import Hypertournaments.Affine.Basic
import Mathlib.Tactic.Abel

/-!
# Linear operations on affine-labelled tuple functions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Differences have the ordinary negation
involution; adding such a difference retains the original affine involution.
-/

universe u v

namespace Hypertournaments.Affine

/-- Subtraction cancels the common affine offset. -/
def Labelled.affineSub {n : ℕ} {G : Type u} [AddCommGroup G] {a : G} {V : Type v}
    (p q : Labelled n (Palette.affine a) V) : Labelled n (Palette.affine (0 : G)) V where
  label t := p.label t - q.label t
  swap_label t i j hij := by
    rw [p.swap_label t i j hij, q.swap_label t i j hij]
    simp only [Palette.affine_star]
    abel

@[simp] theorem Labelled.affineSub_label {n : ℕ} {G : Type u} [AddCommGroup G]
    {a : G} {V : Type v} (p q : Labelled n (Palette.affine a) V) (t : Fin n ↪ V) :
    (p.affineSub q).label t = p.label t - q.label t := rfl

/-- An ordinary alternating term shifts an affine-labelled tuple function. -/
def Labelled.affineAddLinear {n : ℕ} {G : Type u} [AddCommGroup G] {a : G} {V : Type v}
    (p : Labelled n (Palette.affine a) V)
    (s : Labelled n (Palette.affine (0 : G)) V) : Labelled n (Palette.affine a) V where
  label t := p.label t + s.label t
  swap_label t i j hij := by
    rw [p.swap_label t i j hij, s.swap_label t i j hij]
    simp only [Palette.affine_star]
    abel

@[simp] theorem Labelled.affineAddLinear_label {n : ℕ} {G : Type u} [AddCommGroup G]
    {a : G} {V : Type v} (p : Labelled n (Palette.affine a) V)
    (s : Labelled n (Palette.affine (0 : G)) V) (t : Fin n ↪ V) :
    (p.affineAddLinear s).label t = p.label t + s.label t := rfl

/-- The zero ordinary alternating cochain, in every degree and on every carrier. -/
def Labelled.linearZero (n : ℕ) (G : Type u) [AddCommGroup G] (V : Type v) :
    Labelled n (Palette.affine (0 : G)) V where
  label _ := 0
  swap_label _ _ _ _ := by simp

theorem Labelled.affineAddLinear_sub {n : ℕ} {G : Type u} [AddCommGroup G]
    {a : G} {V : Type v} (p q : Labelled n (Palette.affine a) V) :
    q.affineAddLinear (p.affineSub q) = p := by
  apply Labelled.ext
  intro t
  simp only [Labelled.affineAddLinear_label, Labelled.affineSub_label]
  abel

end Hypertournaments.Affine
