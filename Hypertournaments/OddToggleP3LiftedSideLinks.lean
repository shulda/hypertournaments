import Hypertournaments.OddToggleP3FinitePotentialLift
import Hypertournaments.OddToggleP3GenuineSideLinkTransfer

/-!
# Genuine one-point p3 side link orientations as ambient lifted cochains

A preserved true intrinsic one-point side with potential z has
canonical orientation e(Q)=δz(Q) on all n-vertex subsets.
After any order-preserving side vertex embedding g into an actual
joint E, the image's canonical orientation equals the unsigned
coboundary of one explicitly LIFTED ambient potential z'.

This is the canonical sign-level link equality needed in the
all-genuine-joints p3 gauge theorem. The potential lift works
for arbitrary injections; the order-preservation premise
comes only from the canonical sign table naturality.

No side-age or nonamalgamation conclusion is asserted here.
-/

namespace Hypertournaments

/-- The genuine canonical orientation of each side n-set embedded
order-preservingly in a joint equals the coboundary of the lifted
side potential on its actual ambient image. -/
theorem p3SideHyper_jointCanonicalViaLift
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
      coboundary
        (p3LiftFinPotential g.toEmbedding
          (p3SidePotential m t old fresh eligible W L))
        (Q.image g) := by
  calc
    p1BitToZMod (E.canonicalSignTable (Q.image g)) =
      coboundary (p3SidePotential m t old fresh eligible W L) Q :=
        p3SideHyper_jointCanonicalLinkZMod
          m t b c old fresh eligible W L E g hE Q hQ
    _ = coboundary
          (p3LiftFinPotential g.toEmbedding
            (p3SidePotential m t old fresh eligible W L))
          (Q.image g) :=
        (p3LiftFinPotential_coboundary_image
          g.toEmbedding (p3SidePotential m t old fresh eligible W L) Q).symm

end Hypertournaments
