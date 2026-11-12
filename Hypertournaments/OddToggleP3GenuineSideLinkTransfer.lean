import Hypertournaments.OddToggleP3ExplicitPotentials
import Hypertournaments.CanonicalSignTableNaturality
import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Actual one-point side orientation links are canonical F₂ potential facets

A real intrinsic p3 one-point side Hyper is defined by an arbitrary
finite potential z, with orientation signs given by δz.
For every genuine (m+1)-set Q in the side, the ZMod 2 value of its
intrinsic canonical orientation table is exactly δz(Q).

If a hypothetical joint E preserves this side by an ORDER-PRESERVING
vertex embedding g, naturality of the intrinsic canonical sign table
identifies E's orientation on the actual image Q.image g with the
original side coboundary δz(Q).

This is the genuine side-link transport needed to discharge the
left/right endpoint-link hypotheses of the universal mixed gauge.
The chosen order is only used for canonical sign presentation,
not added to the hypertournament language.
-/

namespace Hypertournaments

/-- The side Hyper's real canonical n-set orientation is the
F₂ coboundary of its actual finite-set side potential. -/
theorem p3SideHyper_canonicalZMod
    (m t b : ℕ)
    (old : Fin (m*t) ↪ Fin b) (fresh : Fin b)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset (Fin b)) (hQ : Q.card = m+1) :
    p1BitToZMod
      ((p3SideHyper m t old fresh eligible W L).canonicalSignTable Q) =
      coboundary (p3SidePotential m t old fresh eligible W L) Q := by
  change p1BitToZMod
      ((p3HyperFromPotential (m+1) b
          (p3SidePotential m t old fresh eligible W L)).canonicalSignTable Q) =
      coboundary (p3SidePotential m t old fresh eligible W L) Q
  exact p3HyperFromPotential_canonicalZMod
    (m+1) b (p3SidePotential m t old fresh eligible W L) Q hQ

/-- Every order-preserving intrinsic embedding of an actual
one-point side into a hypothetical joint transports its
canonical orientation bits with no loss or sign ambiguity. -/
theorem p3SideHyper_jointCanonicalLinkZMod
    (m t b c : ℕ)
    (old : Fin (m*t) ↪ Fin b) (fresh : Fin b)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (E : Hyper (m+1) (Fin c))
    (g : Fin b ↪o Fin c)
    (hE : Preserves (p3SideHyper m t old fresh eligible W L)
      E g.toEmbedding)
    (Q : Finset (Fin b)) (hQ : Q.card = m+1) :
    p1BitToZMod (E.canonicalSignTable (Q.image g)) =
      coboundary (p3SidePotential m t old fresh eligible W L) Q := by
  calc
    p1BitToZMod (E.canonicalSignTable (Q.image g)) =
        p1BitToZMod
          ((p3SideHyper m t old fresh eligible W L).canonicalSignTable Q) := by
          rw [Hyper.canonicalSignTable_image_orderEmbedding
            (p3SideHyper m t old fresh eligible W L)
            E g hE Q]
    _ = coboundary (p3SidePotential m t old fresh eligible W L) Q :=
      p3SideHyper_canonicalZMod m t b old fresh eligible W L Q hQ

end Hypertournaments
