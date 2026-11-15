import Hypertournaments.OddToggleP3ShiftedBadPatternMembership
import Hypertournaments.OddToggleP3ActualParentRawFacetDictionary
import Hypertournaments.OddToggleP3AlternatingPrefixForbidden
import Hypertournaments.OddToggleP3ActualBadPatternRightEndpoint
import Hypertournaments.OddToggleP3CanonicalEndpointBoolTransport
import Hypertournaments.OddToggleP3ToggleToSwitching

/-!
# A gauge-shifted bad RAW source trial forbids every genuine p3 joint

Fix an actual intrinsic p3 joint E preserving the canonical RIGHT
one-point side. A selected zero-sum trial q gives a literal
increasing (n+1)-parent with the first m raw facet signs equal
to the actual selected mixed-facet orientation bits, and the
penultimate raw facet equal to the genuine RIGHT endpoint sign.

If those mixed orientation bits are link-source(q,i) XOR shift(i),
and the RAW selected full source word is in the two-pattern bad
set shifted by shift, then after the shift the interior raw
facet signs alternate with phase b. The certified genuine
endpoint source formula says that the actual right endpoint
raw sign equals b. Since E is switching-admissible, parity
forces the final endpoint sign to equal !b, so this real
parent packet is homogeneous and forbidden.

This deterministic implication uses the actual finite packet,
actual intrinsic signs, and actual preserved side. It is
independent of the probability argument and does not assume a
preferred joint.
-/

namespace Hypertournaments

open scoped Classical

/-- For any actual admissible p3 joint preserving the real
right one-point side, a selected RAW source word in the
gauge-shifted bad set is incompatible with the actual
selected mixed-facet orientation shift. -/
theorem Hyper.p3ActualShiftedBadTrial_impossible
    (k t : ℕ) (ht : 0 < t)
    (eligibleR : Finset (Fin (4*k+2)))
    (bits : p3FullSourceSpace (ZMod t) (4*k+1) → Bool)
    (E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+3))) E)
    (hR : Preserves
      (p3CanonicalSide (4*k+2) t eligibleR
        (p3RealWFromSources (4*k+1) t ht bits)
        (p3RealLinkFromSources (4*k+1) t ht bits))
      E (rightJointInclusion ((4*k+2)*t)))
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (shift : Fin (4*k+2) → Bool)
    (hMixed : ∀ i : Fin (4*k+2),
      E.canonicalSignTable (p3ActualSelectedMixedSet k t ht q i) =
        (bits (p3FullTrialSourceIndex (4*k+1) (q,Sum.inl i)) ^^ shift i))
    (hBad :
      (fun p : Fin (4*k+2) ⊕ Unit =>
        bits (p3FullTrialSourceIndex (4*k+1) (q,p))) ∈
      p3ShiftedBadTrialPatternSet (4*k+2) shift
        (p3FixedBadWChoice (4*k+2) shift
          (p3EligibleLinkParity (4*k+1) eligibleR))) :
    False := by
  classical
  let m : ℕ := 4*k+2
  let s : ℕ := 4*k+1
  let a : ℕ := m*t
  let W : Finset (Fin a) → ZMod 2 :=
    p3RealWFromSources s t ht bits
  let Link : Finset (Fin a) → ZMod 2 :=
    p3RealLinkFromSources s t ht bits
  let sourceWord : p3TrialPatternWord m :=
    fun p => bits (p3FullTrialSourceIndex s (q,p))
  let choice : Bool → Bool :=
    p3FixedBadWChoice m shift (p3EligibleLinkParity s eligibleR)
  have hRaw : sourceWord ∈
      p3ShiftedBadTrialPatternSet m shift choice := hBad
  have hTransformed :=
    (p3ShiftedBadTrialPattern_mem_iff m shift choice sourceWord).mp hRaw
  have hWord :
      p3ShiftTrialWord m shift sourceWord =
      p3TrialPacketBits m
        (p3BoolTranslate shift (p3ActualSelectedLinkWord s bits q))
        (bits (p3FullTrialSourceIndex s (q,Sum.inr ()))) := by
    funext p
    cases p with
    | inl i => rfl
    | inr u => cases u; rfl
  have hActualBad :
      p3TrialPacketBits m
        (p3BoolTranslate shift (p3ActualSelectedLinkWord s bits q))
        (bits (p3FullTrialSourceIndex s (q,Sum.inr ()))) ∈
      ((Finset.univ : Finset Bool).image
        (p3BadPattern m choice)) := by
    rw [hWord] at hTransformed
    exact hTransformed
  obtain ⟨phase,hPhase,hSideRight⟩ :=
    (p3ActualSelectedRightEndpoint_badPattern_iff
      s t ht eligibleR bits q shift).mp hActualBad
  obtain ⟨f,_,hOld,hRightFacet,_⟩ :=
    E.p3ActualSelectedParent_has_raw_facet_dictionary k t ht q
  have hInterior : ∀ i : Fin m,
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
        p3AlternatingWord m phase i := by
    intro i
    calc
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
          E.canonicalSignTable (p3ActualSelectedMixedSet k t ht q i) :=
        hOld i
      _ = (bits (p3FullTrialSourceIndex s (q,Sum.inl i)) ^^ shift i) :=
        hMixed i
      _ = p3AlternatingWord m phase i :=
        congrFun hPhase i
  let Q : Finset (Fin a) :=
    p3CoordinateTransversal m t ht q.1
  have hActualRight :=
    p3CanonicalJoint_right_endpointBool_of_preserves
      m t eligibleR W Link E hR Q
  have hBeta :
      E.orient (facet f.toEmbedding ((Fin.last m).castSucc)) = phase := by
    calc
      E.orient (facet f.toEmbedding ((Fin.last m).castSucc)) =
        E.canonicalSignTable
          (insert (Fin.last (a+1))
            (Q.image ((onePointBaseEmbedding a).trans
              (leftJointInclusion a)))) := hRightFacet
      _ = (p3CanonicalSide m t eligibleR W Link).canonicalSignTable
          (insert (Fin.last a)
            (Q.image (onePointBaseEmbedding a))) := hActualRight
      _ = phase := hSideRight
  have hSwitch : localIndex E f.toEmbedding ∈
      switchingAllowed (4*k+3) :=
    (E.p3ToggleAdmissible_switchingAllowed
      k (a+2) hE) f.toEmbedding
  have hForbidden :=
    E.p3Switching_alternating_prefix_right_forbidden
      k (a+2) f hSwitch phase hInterior hBeta
  exact hForbidden (hE f.toEmbedding)

end Hypertournaments
