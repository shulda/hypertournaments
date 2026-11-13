import Hypertournaments.OddToggleP3AlternatingPrefixForbidden
import Hypertournaments.OddToggleP3FixedBadWChoice

/-!
# Every certified fixed-bad-W source pattern contradicts a real p3 switching packet

For any INTRINSIC increasing arity-(4k+3) packet, suppose the
first m=4k+2 actual raw facet orientations equal the Boolean
XOR-shift of a source link word by a fixed gauge word, and
the penultimate raw facet (deletion of the left fresh point)
equals a base W bit XOR the deterministic right-link parity
of that word.

The exact already kernel-checked two-phase bad-W source-pattern
equivalence then implies the first m raw facets alternate with
phase b and the penultimate raw facet has sign b. Genuine
switching parity forces the last raw facet to have sign !b;
the whole packet is homogeneous local type zero and excluded
by toggleZero. No probability or preferred completion is used.

The sole remaining application task is to discharge these TWO
actual raw-facet source-identification premises via the
canonical selected parent ordered packet and genuine side maps.
-/

namespace Hypertournaments

/-- A fixed phase-dependent forbidden source word is
incompatible with any actual switching packet whose TRUE
mixed raw facets and right endpoint are correctly read from
that source word. -/
theorem Hyper.p3FixedBadPattern_forbids_actual_switching_packet
    (k a : ℕ) (E : Hyper (4*k+3) (Fin a))
    (f : Fin (4*k+4) ↪o Fin a)
    (hSwitch : localIndex E f.toEmbedding ∈
      switchingAllowed (4*k+3))
    (shift link : Fin (4*k+2) → Bool)
    (rightSum : (Fin (4*k+2) → Bool) → Bool)
    (base : Bool)
    (hInterior : ∀ i : Fin (4*k+2),
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
        p3BoolTranslate shift link i)
    (hBeta :
      E.orient (facet f.toEmbedding
        ((Fin.last (4*k+2)).castSucc)) =
          (base ^^ rightSum link))
    (hBad :
      p3TrialPacketBits (4*k+2) (p3BoolTranslate shift link) base ∈
        ((Finset.univ : Finset Bool).image
          (p3BadPattern (4*k+2)
            (p3FixedBadWChoice (4*k+2) shift rightSum)))) :
    localIndex E f.toEmbedding ∉
      toggleZero (switchingAllowed (4*k+3)) := by
  obtain ⟨phase,hAlt,hEnd⟩ :=
    (p3RightEndpoint_badEvent_iff_badPatterns
      (4*k+2) shift link rightSum base).mpr hBad
  have hOldAlt : ∀ i : Fin (4*k+2),
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
        p3AlternatingWord (4*k+2) phase i := by
    intro i
    exact (hInterior i).trans (congrFun hAlt i)
  have hBetaAlt :
      E.orient (facet f.toEmbedding
        ((Fin.last (4*k+2)).castSucc)) = phase :=
    hBeta.trans hEnd
  exact E.p3Switching_alternating_prefix_right_forbidden
    k a f hSwitch phase hOldAlt hBetaAlt

end Hypertournaments
