import Hypertournaments.OddToggleP3ActualSelectedJointSourceGauge
import Hypertournaments.OddToggleP3BitAndMixedFacetBridge

/-!
# The genuine selected p3 mixed facet sign is a Boolean-shifted source

The true mixed intrinsic canonical orientation of the actual
set containing both fresh vertices and the punctured selected
old transversal equals its nested canonical cochain contraction.
This is checked from explicit disjointness of the two new
vertices and old image, without any synthetic mixed completion.

Combining the universal real selected source/gauge theorem and
the F₂-to-Boolean XOR identity yields the exact Boolean
orientation bit of *every selected actual mixed facet* as the
independent global link bit XOR the fixed gauge shift, using ONE
gauge simultaneously for all selected zero-sum trials.
-/

namespace Hypertournaments

open scoped Classical

/-- Literal selected genuine mixed n-set: two actual canonical
fresh vertices and the selected punctured old transversal. -/
def p3ActualSelectedMixedSet
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) :
    Finset (Fin ((4*k+2)*t+2)) :=
  let a : ℕ := (4*k+2)*t
  let U : Finset (Fin a) :=
    p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  insert ((Fin.last a).castSucc)
    (insert (Fin.last (a+1)) (U.image old))

/-- The nested cochain contraction from the universal joint
gauge theorem is exactly the canonical intrinsic orientation
of the literal genuine selected mixed n-set. -/
theorem p3ActualSelectedMixedCanonicalBit_trueSign
    (k t : ℕ) (ht : 0 < t)
    (E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)))
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) :
    p3ActualSelectedMixedCanonicalBit k t ht E q i =
      p1BitToZMod
        (E.canonicalSignTable (p3ActualSelectedMixedSet k t ht q i)) := by
  classical
  let a : ℕ := (4*k+2)*t
  let U : Finset (Fin a) :=
    p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  have hlr : l ≠ r := Fin.castSucc_ne_last (Fin.last a)
  have hl : l ∉ U.image old := by
    intro hm
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
    change v.castSucc.castSucc = (Fin.last a).castSucc at hv
    have hEq : v.castSucc = Fin.last a :=
      (Fin.castSuccEmb : Fin (a+1) ↪ Fin (a+2)).injective hv
    exact Fin.castSucc_ne_last v hEq
  have hr : r ∉ U.image old := by
    intro hm
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
    change v.castSucc.castSucc = Fin.last (a+1) at hv
    exact Fin.castSucc_ne_last (v.castSucc) hv
  change
    contractAt r
      (contractAt l
        (fun T : Finset (Fin (a+2)) =>
          p1BitToZMod (E.canonicalSignTable T)))
      (U.image old) =
    p1BitToZMod
      (E.canonicalSignTable (insert l (insert r (U.image old))))
  exact p3DoubleContractAt_eq_mixedSet l r hlr
    (fun T => p1BitToZMod (E.canonicalSignTable T))
    (U.image old) hl hr

/-- Every genuine joint preserving the two complementary real
one-point sides has ONE gauge u whose Boolean orientation bit
on each ACTUAL selected mixed facet is the globally independent
link source bit XOR the gauge shift at that facet. -/
theorem Hyper.p3ActualSelectedJoint_has_boolean_source_shift
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
        E.canonicalSignTable (p3ActualSelectedMixedSet k t ht q i) =
          bits (p3FullTrialSourceIndex (4*k+1) (q,Sum.inl i)) ^^
          p3ZMod2ToBool (coboundary u
            (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i))) := by
  obtain ⟨u,hu⟩ :=
    E.p3ActualSelectedJoint_has_independent_source_gauge
      k t ht root eligible bits hE hL hR
  refine ⟨u, ?_⟩
  intro q i
  have hSource := hu q i
  rw [p3ActualSelectedMixedCanonicalBit_trueSign k t ht E q i] at hSource
  have hBool := congrArg p3ZMod2ToBool hSource
  simpa only [p3Bool_of_bitToZMod, p3Bool_of_source_plus_gauge] using hBool

end Hypertournaments
