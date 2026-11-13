import Hypertournaments.OddToggleP3CanonicalLiftContracts
import Hypertournaments.OddToggleP3RealSelectedMixedSource
import Hypertournaments.OddToggleP3ToggleToSwitching

/-!
# Genuine canonical p3 mixed facets equal real random bits plus one gauge

An arbitrary true intrinsic joint E preserving both canonical
potential-induced one-point sides belongs to the switching age
whenever it belongs to the smaller homogeneous-free age.
The already certified all-joints gauge theorem then gives one
cochain u on the common old base such that the mixed canonical
cochain equals the contractions of both lifted side potentials
plus δu, simultaneously on ALL old (m-1)-sets.

The real contraction lemmas evaluate these terms as the actual
eligible L/R coefficients. The complementary selected-facet
lemma identifies their sum with the exact globally independent
source bit. Thus ONE u works on all selected zero-sum old facets.

This does not assert the final forbidden-packet argument or
non-amalgamation; it discharges the genuine source/gauge bridge.
-/

namespace Hypertournaments

open scoped Classical

/-- The actual F₂ canonical orientation of the mixed (n=4k+3)
facet with both new vertices and the selected q-facet of old
vertices obtained by deleting coordinate i. -/
def p3ActualSelectedMixedCanonicalBit
    (k t : ℕ) (ht : 0 < t)
    (E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)))
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) : ZMod 2 :=
  let a : ℕ := (4*k+2)*t
  let U : Finset (Fin a) :=
    p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  contractAt (Fin.last (a+1))
    (contractAt ((Fin.last a).castSucc)
      (fun T : Finset (Fin (a+2)) =>
        p1BitToZMod (E.canonicalSignTable T)))
    (U.image old)

/-- Every genuine canonical joint in the p3 forbidden-homogeneous
age preserving both real one-point sides has ONE gauge u such
that ALL selected mixed facet orientations are their globally
independent link source bits plus the coboundary of u. -/
theorem Hyper.p3ActualSelectedJoint_has_independent_source_gauge
    (k t : ℕ) (ht : 0 < t)
    (root : Fin ((4*k+2)*t))
    (eligible : Finset (Fin (4*k+2)))
    (bits : p3FullSourceSpace (ZMod t) (4*k+1) → Bool)
    (E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+3))) E)
    (hL : Preserves
      (p3CanonicalSide (4*k+2) t eligible
        (p3RealWFromSources (4*k+1) t ht bits)
        (p3RealLinkFromSources (4*k+1) t ht bits))
      E (leftJointInclusion ((4*k+2)*t)))
    (hR : Preserves
      (p3CanonicalSide (4*k+2) t (Finset.univ \ eligible)
        (p3RealWFromSources (4*k+1) t ht bits)
        (p3RealLinkFromSources (4*k+1) t ht bits))
      E (rightJointInclusion ((4*k+2)*t))) :
    ∃ u : Finset (Fin ((4*k+2)*t)) → ZMod 2,
      ∀ (q : p3SelectedTrials (ZMod t) (4*k+1))
        (i : Fin (4*k+2)),
        p3ActualSelectedMixedCanonicalBit k t ht E q i =
          p1BitToZMod
            (bits (p3FullTrialSourceIndex (4*k+1) (q,Sum.inl i))) +
          coboundary u
            (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)) := by
  classical
  let m : ℕ := 4*k+2
  let s : ℕ := 4*k+1
  let a : ℕ := m*t
  let W : Finset (Fin a) → ZMod 2 :=
    p3RealWFromSources s t ht bits
  let Link : Finset (Fin a) → ZMod 2 :=
    p3RealLinkFromSources s t ht bits
  have hSwitch : Admissible (switchingAllowed (4*k+3)) E :=
    E.p3ToggleAdmissible_switchingAllowed k (a+2) hE
  obtain ⟨u,hu⟩ :=
    E.p3CanonicalPreservedJoint_has_mixed_gauge
      k t root hSwitch eligible (Finset.univ \ eligible)
      W Link Link hL hR
  refine ⟨u, ?_⟩
  intro q i
  let U : Finset (Fin a) :=
    p3ActualPunctureSubsetIndex s t ht (q,i)
  have hcard : U.card = 4*k+1 := by
    have hh := (p3CoordinatePuncture_isEligibleMissing
      m t ht (Finset.univ : Finset (Fin m)) q.1 i
      (Finset.mem_univ i)).1
    change U.card = m-1 at hh
    dsimp only [m] at hh
    omega
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let leftNew : Fin (a+2) := (Fin.last a).castSucc
  let rightNew : Fin (a+2) := Fin.last (a+1)
  let zL : Finset (Fin (a+2)) → ZMod 2 :=
    p3LiftFinPotential (leftJointInclusion a)
      (p3SidePotential m t (onePointBaseEmbedding a)
        (Fin.last a) eligible W Link)
  let zR : Finset (Fin (a+2)) → ZMod 2 :=
    p3LiftFinPotential (rightJointInclusion a)
      (p3SidePotential m t (onePointBaseEmbedding a)
        (Fin.last a) (Finset.univ \ eligible) W Link)
  have hg :
      p3ActualSelectedMixedCanonicalBit k t ht E q i =
        (contractAt leftNew zL (U.image old) +
          contractAt rightNew zR (U.image old)) +
        coboundary u U := hu U hcard
  have hl :
      contractAt leftNew zL (U.image old) =
        if p3IsEligibleMissingTransversal m t eligible U
        then Link U else 0 :=
    p3CanonicalLeftLift_contractAt_old m t eligible W Link U
  have hr :
      contractAt rightNew zR (U.image old) =
        if p3IsEligibleMissingTransversal m t
            (Finset.univ \ eligible) U
        then Link U else 0 :=
    p3CanonicalRightLift_contractAt_old m t
      (Finset.univ \ eligible) W Link U
  have hs :
      (if p3IsEligibleMissingTransversal m t eligible U
        then Link U else 0) +
      (if p3IsEligibleMissingTransversal m t
          (Finset.univ \ eligible) U
        then Link U else 0) =
      p1BitToZMod
        (bits (p3FullTrialSourceIndex s (q,Sum.inl i))) :=
    p3RealSelectedTwoSideFacet_eq_linkSource s t ht eligible bits q i
  rw [hl,hr,hs] at hg
  exact hg

end Hypertournaments
