import Hypertournaments.Affine.Basic
import Hypertournaments.Affine.SignedCoboundary
import Mathlib.Tactic.Ext

/-!
# Data and expansions for the affine coboundary construction

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". No finiteness assumption is needed
for the palette map, closedness, or a specified potential.
-/

universe u v w z

namespace Hypertournaments.Affine

/-- An involutive palette mapping onto an affine group palette. -/
structure Data (Q : Type u) (G : Type v) [AddCommGroup G] where
  palette : Palette Q
  offset : G
  effective : Q → G
  map_star : ∀ q, effective (palette.star q) = offset - effective q
  onto : Function.Surjective effective

/-- Effective labels satisfy the signed cocycle equation. -/
def Closed {Q : Type u} {G : Type v} [AddCommGroup G]
    (d : Data Q G) {n : ℕ} {V : Type w} (raw : Labelled n d.palette V) : Prop :=
  ∀ t : Fin (n + 1) ↪ V,
    signedCoboundary (fun s => d.effective (raw.label s)) t = 0

/-- A specified affine-labelled potential has the prescribed effective
coboundary on every injective tuple. -/
def IsPotential {Q : Type u} {G : Type v} [AddCommGroup G]
    (d : Data Q G) {r : ℕ} {V : Type w}
    (raw : Labelled (r + 1) d.palette V)
    (p : Labelled r (Palette.affine d.offset) V) : Prop :=
  ∀ t : Fin (r + 1) ↪ V,
    signedCoboundary p.label t = d.effective (raw.label t)

/-- A raw structure expanded by one actual affine potential. -/
structure Expansion {Q : Type u} {G : Type v} [AddCommGroup G]
    (r : ℕ) (d : Data Q G) (V : Type w) where
  raw : Labelled (r + 1) d.palette V
  potential : Labelled r (Palette.affine d.offset) V
  compatible : IsPotential d raw potential

@[ext] theorem Expansion.ext {Q : Type u} {G : Type v} [AddCommGroup G]
    {r : ℕ} {d : Data Q G} {V : Type w} {A B : Expansion r d V}
    (hraw : A.raw = B.raw) (hpotential : A.potential = B.potential) : A = B := by
  cases A
  cases B
  cases hraw
  cases hpotential
  rfl

/-- Finite palettes give only finitely many actual expansions on a fixed
finite carrier. -/
instance Expansion.finite {Q : Type u} {G : Type v} [AddCommGroup G]
    [Finite Q] [Finite G] {r : ℕ} {d : Data Q G} {V : Type w} [Finite V] :
    Finite (Expansion r d V) :=
  Finite.of_injective (fun A : Expansion r d V => (A.raw, A.potential))
    (fun _ _ h => Expansion.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Both named label structures are preserved by the original injection. -/
def Expansion.Preserves {Q : Type u} {G : Type v} [AddCommGroup G]
    {r : ℕ} {d : Data Q G} {V : Type w} {W : Type z}
    (A : Expansion r d V) (B : Expansion r d W) (e : V ↪ W) : Prop :=
  A.raw.Preserves B.raw e ∧ A.potential.Preserves B.potential e

end Hypertournaments.Affine
