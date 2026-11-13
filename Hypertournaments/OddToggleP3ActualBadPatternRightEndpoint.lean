import Hypertournaments.OddToggleP3ActualEndpointSourceWord
import Hypertournaments.OddToggleP3FixedBadWChoice

/-!
# The actual selected right endpoint has the exact fixed bad-W source pattern

For a canonical p3 one-point side, the genuine endpoint sign on
the old full zero-sum transversal Q equals independent W(q) XOR
the deterministic eligible link parity of the complete selected
link word. Fix ANY Boolean shift (to be supplied by a real mixed
joint gauge). The prior kernel-certified p3FixedBadWChoice
algebra then identifies the two forbidden source patterns with:
  - shifted selected link word alternating with phase b;
  - TRUE right-side canonical endpoint orientation equal to b.

This is an exact equivalence about genuine side orientations,
not a synthetic endpoint test or a probabilistic assertion.
-/

namespace Hypertournaments

open scoped Classical

/-- The actual right canonical side endpoint is compatible with
an alternating shifted selected mixed interior if and only if
the complete independent global source word matches one of the
two fixed phase-dependent forbidden W choices. -/
theorem p3ActualSelectedRightEndpoint_badPattern_iff
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s)
    (shift : Fin (s+1) → Bool) :
    p3TrialPacketBits (s+1)
      (p3BoolTranslate shift (p3ActualSelectedLinkWord s bits q))
      (bits (p3FullTrialSourceIndex s (q,Sum.inr ()))) ∈
        ((Finset.univ : Finset Bool).image
          (p3BadPattern (s+1)
            (p3FixedBadWChoice (s+1) shift
              (p3EligibleLinkParity s eligible)))) ↔
      ∃ phase : Bool,
        p3BoolTranslate shift (p3ActualSelectedLinkWord s bits q) =
          p3AlternatingWord (s+1) phase ∧
        (p3CanonicalSide (s+1) t eligible
            (p3RealWFromSources s t ht bits)
            (p3RealLinkFromSources s t ht bits)).canonicalSignTable
          (insert (Fin.last ((s+1)*t))
            ((p3CoordinateTransversal (s+1) t ht q.1).image
              (onePointBaseEmbedding ((s+1)*t)))) = phase := by
  classical
  have hRight :=
    p3ActualSelectedCanonicalSide_endpointBool_eq_W_xor_linkParity
      s t ht eligible bits q
  rw [hRight]
  exact (p3RightEndpoint_badEvent_iff_badPatterns
    (s+1) shift (p3ActualSelectedLinkWord s bits q)
    (p3EligibleLinkParity s eligible)
    (bits (p3FullTrialSourceIndex s (q,Sum.inr ())))).symm

end Hypertournaments
