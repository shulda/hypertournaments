import Lean.Elab.Tactic.Omega
import Hypertournaments.TwoPadOrdinaryAPTransfer

/-!
# Reflection preserves genuine disagreement between one-point sides

The generic ordinary AP transfer previously required the higher
lifted source sides to disagree on some (n+2)-tuple, so that their
new vertices could not be identified in an ordinary amalgam.

This follows from the lower source disagreement and the exact two-pad
recovery hypothesis, as soon as there are at least two auxiliary
pads. The profile pigeonhole bound already guarantees that.

Thus ordinary non-AP transfer can be formulated in terms of the
original lower diagram only; no additional higher disagreement
certificate is necessary.
-/

namespace Hypertournaments

/-- Exact recovery of lower source signs detects any orientation
disagreement of the lower one-point sides inside the lifted sides. -/
theorem canonical_twoPad_disagreement_of_low_disagreement
    {n a m : ℕ}
    (L R : Hyper n (Fin (a + 1)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1)))
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (hrec : CanonicalTwoPadSideRecovery n a m L R BL BR)
    (hlow : ∃ t : Fin n ↪ Fin (a + 1), L.orient t ≠ R.orient t) :
    ∃ t : Fin (n + 2) ↪ Fin (m + a + 1),
      BL.orient t ≠ BR.orient t := by
  have hp : 0 < (2 : ℕ) ^
      Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) :=
    pow_pos (by decide) _
  have hm2 : 1 < m := by omega
  let x : Fin m := ⟨0, by omega⟩
  let y : Fin m := ⟨1, by omega⟩
  have hlt : x < y := by
    change (0 : ℕ) < 1
    decide
  have hxy : x ≠ y := ne_of_lt hlt
  obtain ⟨t, hdiff⟩ := hlow
  let u : Fin (n + 2) ↪ Fin (m + a + 1) :=
    twoPadSliceTuple
      (canonicalOldToSide m a)
      (canonicalPadToSide m a x)
      (canonicalPadToSide m a y)
      (canonicalPadToSide_not_mem_old m a x)
      (canonicalPadToSide_not_mem_old m a y)
      (fun he => hxy ((canonicalPadToSide m a).injective he)) t
  refine ⟨u, ?_⟩
  have hL : BL.orient u = L.orient t := hrec.1 x y hlt t
  have hR : BR.orient u = R.orient t := hrec.2 x y hlt t
  intro he
  exact hdiff (hL.symm.trans (he.trans hR))

/-- Ordinary AP obstruction transfer under exact two-pad source
recovery, with no separate disagreement assumption on the lifted
sides: disagreement is inherited from the lower source diagram. -/
theorem not_hasAP_of_twoPad_lift_with_lower_disagreement
    {n a m : ℕ} (S T : Set ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (Ahi : Hyper (n + 2) (Fin (m + a)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1)))
    (hAhi : Admissible T Ahi)
    (hBLad : Admissible T BL) (hBRad : Admissible T BR)
    (hAL : Preserves Ahi BL (onePointBaseEmbedding (m + a)))
    (hAR : Preserves Ahi BR (onePointBaseEmbedding (m + a)))
    (hlow : ∃ t : Fin n ↪ Fin (a + 1), L.orient t ≠ R.orient t)
    (hNoLow : ∀ E : Hyper n (Fin (a + 2)),
        Admissible S E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (hrec : CanonicalTwoPadSideRecovery n a m L R BL BR) :
    ¬ HasAP (n + 2) T := by
  exact not_hasAP_of_canonical_twoPad_lift S T L R
    Ahi BL BR hAhi hBLad hBRad hAL hAR
    (canonical_twoPad_disagreement_of_low_disagreement
      L R BL BR hm hrec hlow)
    hNoLow hshift hm hrec

end Hypertournaments
