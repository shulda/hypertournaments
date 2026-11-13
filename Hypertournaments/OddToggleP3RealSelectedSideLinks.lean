import Hypertournaments.OddToggleP3RealSelectedLinkFacets
import Hypertournaments.OddToggleP3ActualSideLinkSource

/-!
# Exact source-bit formula for each genuine selected canonical one-point link

For every selected zero-sum coordinate word q, the actual old
full block transversal Q has one old vertex per block. The
canonical one-new facet of the genuine potential-induced p3
side is W(Q) + delta L_eligible(Q).

The previous kernel-level bridge identifies W(Q) with the global
full source bit and each eligible deletion coefficient with the
corresponding unique global punctured link bit. Summing over
the actual vertices of Q proves the *literal* side orientation
source formula. This is the concrete source/geometry interface
for the already formalized global finite probability count.
-/

namespace Hypertournaments

/-- For an actual selected zero-sum transversal, the coboundary
of the side's eligible missing-block link potential is precisely
the sum of the selected independent global link bits in that
eligible half. -/
theorem p3RealSelectedLink_coboundary_eq_sourceSum
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) :
    coboundary
      (fun U : Finset (Fin ((s+1)*t)) =>
        if p3IsEligibleMissingTransversal (s+1) t eligible U
        then p3RealLinkFromSources s t ht bits U else 0)
      (p3CoordinateTransversal (s+1) t ht q.1) =
    ∑ i : Fin (s+1),
      if i ∈ eligible then
        p1BitToZMod
          (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
      else 0 := by
  classical
  let T : Finset (Fin ((s+1)*t)) :=
    p3CoordinateTransversal (s+1) t ht q.1
  let e : Fin (s+1) ↪ Fin ((s+1)*t) :=
    ⟨fun i => p3BlockCoordinateVertex (s+1) t ht i (q.1 i),
      p3CoordinateTransversal_vertex_injective (s+1) t ht q.1⟩
  let F : Finset (Fin ((s+1)*t)) → ZMod 2 :=
    fun U =>
      if p3IsEligibleMissingTransversal (s+1) t eligible U
      then p3RealLinkFromSources s t ht bits U else 0
  have hT : T = (Finset.univ : Finset (Fin (s+1))).image e := rfl
  have hInj : Set.InjOn (e : Fin (s+1) → Fin ((s+1)*t))
      (↑(Finset.univ : Finset (Fin (s+1)))) := by
    intro i _ j _ hij
    exact e.injective hij
  have hsum :
      (∑ v ∈ T, F (T.erase v)) =
      ∑ i ∈ (Finset.univ : Finset (Fin (s+1))),
        F (T.erase (e i)) := by
    calc
      (∑ v ∈ T, F (T.erase v)) =
          ∑ v ∈ (Finset.univ : Finset (Fin (s+1))).image e,
            F (T.erase v) := by rw [hT]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin (s+1))),
            F (T.erase (e i)) := by
          simpa using
            (Finset.sum_image
              (s := (Finset.univ : Finset (Fin (s+1))))
              (g := (e : Fin (s+1) → Fin ((s+1)*t)))
              (f := fun v : Fin ((s+1)*t) => F (T.erase v))
              hInj)
  change coboundary F T =
    ∑ i : Fin (s+1),
      if i ∈ eligible then
        p1BitToZMod
          (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
      else 0
  calc
    coboundary F T = (∑ v ∈ T, F (T.erase v)) := rfl
    _ = ∑ i ∈ (Finset.univ : Finset (Fin (s+1))),
          F (T.erase (e i)) := hsum
    _ = ∑ i : Fin (s+1),
          if i ∈ eligible then
            p1BitToZMod
              (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : T.erase (e i) =
          p3ActualPunctureSubsetIndex s t ht (q,i) := rfl
      change (if p3IsEligibleMissingTransversal (s+1) t eligible
           (T.erase (e i))
        then p3RealLinkFromSources s t ht bits (T.erase (e i))
        else 0) = _
      rw [hi]
      exact p3RealSelectedPuncture_linkValue s t ht eligible bits q i

/-- The TRUE canonical orientation bit of every selected
old-plus-fresh facet in a genuine p3 one-point side is the
specified independent W bit plus precisely the eligible
punctured link bits. -/
theorem p3RealSelectedCanonicalSide_link_eq_globalSources
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) :
    p1BitToZMod
      ((p3CanonicalSide (s+1) t eligible
          (p3RealWFromSources s t ht bits)
          (p3RealLinkFromSources s t ht bits)).canonicalSignTable
        (insert (Fin.last ((s+1)*t))
          ((p3CoordinateTransversal (s+1) t ht q.1).image
            (onePointBaseEmbedding ((s+1)*t))))) =
    p1BitToZMod
      (bits (p3FullTrialSourceIndex s (q,Sum.inr ()))) +
    ∑ i : Fin (s+1),
      if i ∈ eligible then
        p1BitToZMod
          (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
      else 0 := by
  have hQ : p3IsBlockTransversal (s+1) t
      (p3CoordinateTransversal (s+1) t ht q.1) :=
    p3CoordinateTransversal_isBlockTransversal (s+1) t ht q.1
  have hSide := p3CanonicalSide_link_on_full_transversal
    (s+1) t eligible
    (p3RealWFromSources s t ht bits)
    (p3RealLinkFromSources s t ht bits)
    (p3CoordinateTransversal (s+1) t ht q.1) hQ
  rw [p3RealWFromSources_selected s t ht bits q,
    p3RealSelectedLink_coboundary_eq_sourceSum s t ht eligible bits q] at hSide
  exact hSide

end Hypertournaments
