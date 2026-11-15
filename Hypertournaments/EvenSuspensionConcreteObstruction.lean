import Hypertournaments.EvenSuspensionAdmissibility
import Hypertournaments.EvenSuspensionBasePreservation
import Hypertournaments.EvenSuspensionSideRecovery
import Hypertournaments.TwoPadDisagreement

/-!
# Concrete even-arity lifting of an ordinary AP obstruction

This module discharges all construction-specific premises of the
generic two-pad AP reflection for the actual even suspension.

The source is a finite canonical one-point diagram whose two sides
disagree in orientation and have no distinct one-point joint.
Every such diagram produces failure of ordinary high-arity AP
under the exact shifted local-type compatibility conditions.

The separate reduction from arbitrary failure of AP to a canonical
one-point obstruction remains an explicit future obligation.
-/

namespace Hypertournaments

theorem not_hasAP_of_concrete_even_suspension
    (k a m : ℕ) (S T : Set ℕ)
    (A : Hyper (2 * k) (Fin a))
    (L R : Hyper (2 * k) (Fin (a + 1)))
    (hA : Admissible S A)
    (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hcentral : k ∈ S)
    (hraise : ∀ d : ℕ, d ∈ S → d + 1 ∈ T)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (2 * k + 1) ↪ Fin (a + 2)) < m)
    (hlow : ∃ t : Fin (2 * k) ↪ Fin (a + 1),
        L.orient t ≠ R.orient t)
    (hNoLow : ∀ E : Hyper (2 * k) (Fin (a + 2)),
        Admissible S E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False) :
    ¬ HasAP (2 * k + 2) T := by
  apply not_hasAP_of_twoPad_lift_with_lower_disagreement
    S T L R
    (A.evenSuspension m a)
    (L.evenSuspension m (a + 1))
    (R.evenSuspension m (a + 1))
    (A.evenSuspension_admissible_of_shift k m a S T hA hcentral hraise)
    (L.evenSuspension_admissible_of_shift k m (a + 1) S T hL hcentral hraise)
    (R.evenSuspension_admissible_of_shift k m (a + 1) S T hR hcentral hraise)
    (Hyper.evenSuspension_preserves_base (m := m) A L hAL)
    (Hyper.evenSuspension_preserves_base (m := m) A R hAR)
    hlow hNoLow hshift hm
    (canonical_twoPad_recovery_evenSuspension (m := m) L R)

end Hypertournaments
