import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3BasePreservation

/-!
# Lifting finite F₂ potentials along arbitrary injective vertex maps

A cochain defined on finite subsets of Fin a can be extended to
finite subsets of Fin b for any injection g:Fin a ↪ Fin b by
evaluating it on the inverse image (inside the finite domain).
This extension is not claimed unique, but is EXACT on every image
of an old finite subset.

The ordinary unsigned coboundary commutes exactly with this
restriction on the image. This is the missing general construction
for obtaining actual ambient joint potentials from genuine
one-point side potentials.

No order preservation or AP assumption is required here.
-/

namespace Hypertournaments

/-- The finite preimage of any ambient subset under an injective
map between finite vertex sets. -/
def p3FinPreimage {a b : ℕ}
    (g : Fin a ↪ Fin b) (T : Finset (Fin b)) : Finset (Fin a) :=
  Finset.univ.filter (fun x => g x ∈ T)

/-- Taking preimages of a genuinely embedded finite subset
recovers it exactly, by injectivity of the vertex map. -/
theorem p3FinPreimage_image {a b : ℕ}
    (g : Fin a ↪ Fin b) (U : Finset (Fin a)) :
    p3FinPreimage g (U.image g) = U := by
  classical
  ext x
  simp only [p3FinPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
    have hxy : y = x := g.injective heq
    simpa [hxy] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- One explicit lift of a finite F₂ potential to any larger finite
vertex set, obtained by evaluating on the old-coordinate preimage. -/
def p3LiftFinPotential {a b : ℕ}
    (g : Fin a ↪ Fin b)
    (z : Finset (Fin a) → ZMod 2) : Finset (Fin b) → ZMod 2 :=
  fun T => z (p3FinPreimage g T)

/-- The explicit lifted potential has the exact original values
on all genuinely embedded old subsets. -/
theorem p3LiftFinPotential_image {a b : ℕ}
    (g : Fin a ↪ Fin b)
    (z : Finset (Fin a) → ZMod 2)
    (U : Finset (Fin a)) :
    p3LiftFinPotential g z (U.image g) = z U := by
  simp [p3LiftFinPotential, p3FinPreimage_image]

/-- The finite-set coboundary of a lifted potential, on images of
old subsets, is exactly the original coboundary. In particular,
a side's genuine canonical orientation signs δz are preserved
without extending its potential preferentially on new vertices. -/
theorem p3LiftFinPotential_coboundary_image {a b : ℕ}
    (g : Fin a ↪ Fin b)
    (z : Finset (Fin a) → ZMod 2)
    (U : Finset (Fin a)) :
    coboundary (p3LiftFinPotential g z) (U.image g) =
      coboundary z U := by
  apply p3Coboundary_image_injective g z (p3LiftFinPotential g z)
  intro Q
  exact p3LiftFinPotential_image g z Q

end Hypertournaments
