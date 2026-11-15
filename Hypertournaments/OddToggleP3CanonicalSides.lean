import Hypertournaments.OddToggleP3BasePreservation
import Hypertournaments.OnePointJoint

/-!
# A genuine canonical one-point span for the p3 random construction

Use the SAME old base of a=m*t vertices in both side structures
Fin(a+1), number the old vertices 0,...,a−1 in their natural
consecutive block order, and assign their new vertex Fin.last a.
This is exactly the one-point span representation used by the
ordinary AP/identification and canonical union lemmas.

The two side coefficient families L,R and their eligible missing
block sets may be completely different, but both sides preserve
the true intrinsic old Hyper induced by the common W potential.
No random success, side admissibility or AP conclusion is asserted.

Unlike placing the left new point before the old base, this
canonical numbering avoids any side/joint orientation-sign
ambiguity when proving ordinary nonamalgamation.
-/

namespace Hypertournaments

/-- The concrete one-point p3 side on a+1 vertices, a=m*t,
with all old vertices first and its sole new vertex last. -/
noncomputable def p3CanonicalSide
    (m t : ℕ)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2) :
    Hyper (m+1) (Fin (m*t+1)) :=
  p3SideHyper m t
    (Fin.castSuccOrderEmb : Fin (m*t) ↪o Fin (m*t+1)).toEmbedding
    (Fin.last (m*t)) eligible W L

/-- Every such canonical side, regardless of its new-link
coefficients or eligible half, is a genuine orientation-preserving
extension of the same W-induced old base. -/
theorem p3CanonicalSide_preserves_base
    (m t : ℕ)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2) :
    Preserves
      (p3HyperFromPotential (m+1) (m*t) (p3BasePotential m t W))
      (p3CanonicalSide m t eligible W L)
      (onePointBaseEmbedding (m*t)) := by
  have h := p3SideHyper_preserves_base m t
    (Fin.castSuccOrderEmb : Fin (m*t) ↪o Fin (m*t+1))
    (Fin.last (m*t))
    (by
      intro v
      exact Fin.castSucc_ne_last v)
    eligible W L
  exact h

/-- A genuine p3 one-point span with arbitrary left/right
coefficients and eligible halves has one common induced old
base for every orientation, not only a common Boolean potential. -/
theorem p3CanonicalSpan_preserves_base
    (m t : ℕ)
    (eligibleL eligibleR : Finset (Fin m))
    (W L R : Finset (Fin (m*t)) → ZMod 2) :
    Preserves
      (p3HyperFromPotential (m+1) (m*t) (p3BasePotential m t W))
      (p3CanonicalSide m t eligibleL W L)
      (onePointBaseEmbedding (m*t)) ∧
    Preserves
      (p3HyperFromPotential (m+1) (m*t) (p3BasePotential m t W))
      (p3CanonicalSide m t eligibleR W R)
      (onePointBaseEmbedding (m*t)) :=
  ⟨p3CanonicalSide_preserves_base m t eligibleL W L,
   p3CanonicalSide_preserves_base m t eligibleR W R⟩

end Hypertournaments
