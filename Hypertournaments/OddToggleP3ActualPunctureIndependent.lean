import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3CoordinatePunctures
import Hypertournaments.OddToggleP3GlobalAllTrialsExact
import Hypertournaments.OddToggleP3ZeroSumCode

/-!
# Actual selected punctured sources are independent in the real old base

The abstract zero-sum source index has previously been proved injective.
Here the *true subsets* of Fin((s+1)*t) carrying the eligible missing-block
one-point side coefficients are shown to have the same independence.

Each source is the pair (deleted block, punctured actual transversal).
The pair is injective over the entire selected zero-sum code: equal
deleted blocks and equal actual punctures force agreement at all
other block coordinates, and the zero-sum equation recovers the
deleted coordinate. No probability axiom is used.
-/

namespace Hypertournaments

/-- The literal missing-block and actual old finite-set source of
one zero-sum trial with one selected coordinate deleted. -/
def p3ActualPunctureSourceIndex
    (s t : ℕ) (ht : 0 < t)
    (qi : p3SelectedTrials (ZMod t) s × Fin (s+1)) :
    Fin (s+1) × Finset (Fin ((s+1)*t)) :=
  (qi.2,
    (p3CoordinateTransversal (s+1) t ht qi.1.1).erase
      (p3BlockCoordinateVertex (s+1) t ht qi.2 (qi.1.1 qi.2)))

/-- Different selected zero-sum trial coordinates never collide
as true old missing-block potential sources. This upgrades abstract
p3RandomSourceIndex_injective to actual p3 side subsets. -/
theorem p3ActualPunctureSourceIndex_injective
    (s t : ℕ) (ht : 0 < t) :
    Function.Injective (p3ActualPunctureSourceIndex s t ht) := by
  classical
  intro x y hxy
  rcases x with ⟨q,i⟩
  rcases y with ⟨r,j⟩
  have hij : i = j := by
    exact congrArg Prod.fst hxy
  subst j
  have hpuncture :
      (p3CoordinateTransversal (s+1) t ht q.1).erase
        (p3BlockCoordinateVertex (s+1) t ht i (q.1 i)) =
      (p3CoordinateTransversal (s+1) t ht r.1).erase
        (p3BlockCoordinateVertex (s+1) t ht i (r.1 i)) := by
    exact congrArg Prod.snd hxy
  have hagree : ∀ k : Fin (s+1), k ≠ i → q.1 k = r.1 k := by
    intro k hki
    have hleft :
        p3BlockCoordinateVertex (s+1) t ht k (q.1 k) ∈
        (p3CoordinateTransversal (s+1) t ht q.1).erase
          (p3BlockCoordinateVertex (s+1) t ht i (q.1 i)) := by
      rw [p3CoordinateTransversal_erase_vertex]
      apply Finset.mem_image.mpr
      exact ⟨k,
        Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, rfl⟩
    have hright :
        p3BlockCoordinateVertex (s+1) t ht k (q.1 k) ∈
        (p3CoordinateTransversal (s+1) t ht r.1).erase
          (p3BlockCoordinateVertex (s+1) t ht i (r.1 i)) := by
      rw [← hpuncture]
      exact hleft
    rw [p3CoordinateTransversal_erase_vertex] at hright
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hright
    have hjk : j = k := by
      apply Fin.ext
      have hv := congrArg (p3BlockNumber t) hj
      simpa only [p3BlockCoordinateVertex_blockNumber] using hv
    subst j
    exact (p3BlockCoordinateVertex_injective_coordinate
      (s+1) t ht k) hj.symm
  have hqr : q.1 = r.1 :=
    p3ZeroSum_eq_of_agree_except s q.1 r.1 i q.2 r.2 hagree
  have hq : q = r := Subtype.ext hqr
  cases hq
  rfl

end Hypertournaments
