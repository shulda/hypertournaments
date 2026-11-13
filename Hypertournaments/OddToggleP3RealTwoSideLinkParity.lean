import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Hypertournaments.OddToggleP3RealSelectedSideLinks

/-!
# Genuine left-plus-right p3 endpoint link parity on selected trials

A selected real old transversal Q has two genuine one-point-side
endpoint canonical signs. For complementary eligible missing-block
sets, both endpoint links have the same full W(Q) coefficient.
Their sum cancels this base bit in F₂, and the disjoint eligible
halves together contribute ALL independent punctured source bits.

The resulting link-sum identity applies to actual intrinsic side
structures on Fin(mt+1), not an abstract surrogate. It is the
identification-exclusion parity expression used in the exact
finite half-event argument.
-/

namespace Hypertournaments

/-- The actual canonical endpoint sign of one genuine p3 one-point
side, for a selected zero-sum old transversal. -/
noncomputable def p3RealSelectedCanonicalLink
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) : ZMod 2 :=
  p1BitToZMod
    ((p3CanonicalSide (s+1) t eligible
        (p3RealWFromSources s t ht bits)
        (p3RealLinkFromSources s t ht bits)).canonicalSignTable
      (insert (Fin.last ((s+1)*t))
        ((p3CoordinateTransversal (s+1) t ht q.1).image
          (onePointBaseEmbedding ((s+1)*t)))))

/-- With complementary eligible halves, the sum of the genuine
left/right endpoint signs is exactly the total independent
link-source parity. The common W-bit vanishes. -/
theorem p3RealSelectedCanonicalLinks_sum_eq_allLinkSources
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) :
    p3RealSelectedCanonicalLink s t ht eligible bits q +
    p3RealSelectedCanonicalLink s t ht
      (Finset.univ \ eligible) bits q =
    ∑ i : Fin (s+1),
      p1BitToZMod
        (bits (p3FullTrialSourceIndex s (q,Sum.inl i))) := by
  classical
  unfold p3RealSelectedCanonicalLink
  rw [p3RealSelectedCanonicalSide_link_eq_globalSources
       s t ht eligible bits q,
      p3RealSelectedCanonicalSide_link_eq_globalSources
       s t ht (Finset.univ \ eligible) bits q]
  let w : ZMod 2 :=
    p1BitToZMod (bits (p3FullTrialSourceIndex s (q,Sum.inr ())))
  let b : Fin (s+1) → ZMod 2 := fun i =>
    p1BitToZMod (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
  change
    (w + ∑ i : Fin (s+1), if i ∈ eligible then b i else 0) +
    (w + ∑ i : Fin (s+1),
      if i ∈ (Finset.univ \ eligible) then b i else 0) =
    ∑ i : Fin (s+1), b i
  have hzero : w + w = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      w + w = (2 : ZMod 2) * w := by ring
      _ = 0 := by rw [htwo]; simp
  have hparts :
      (∑ i : Fin (s+1), if i ∈ eligible then b i else 0) +
      (∑ i : Fin (s+1),
        if i ∈ (Finset.univ \ eligible) then b i else 0) =
      ∑ i : Fin (s+1), b i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ eligible
    · simp [hi]
    · simp [hi]
  calc
    (w + ∑ i : Fin (s+1), if i ∈ eligible then b i else 0) +
        (w + ∑ i : Fin (s+1),
          if i ∈ (Finset.univ \ eligible) then b i else 0) =
      (w+w) +
        ((∑ i : Fin (s+1), if i ∈ eligible then b i else 0) +
         (∑ i : Fin (s+1),
            if i ∈ (Finset.univ \ eligible) then b i else 0)) := by abel
    _ = (∑ i : Fin (s+1), if i ∈ eligible then b i else 0) +
         (∑ i : Fin (s+1),
            if i ∈ (Finset.univ \ eligible) then b i else 0) := by
        rw [hzero]; simp
    _ = ∑ i : Fin (s+1), b i := hparts

end Hypertournaments
