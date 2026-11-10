import Hypertournaments.OddToggleP1PadCorePartition
import Hypertournaments.OddToggleP1CanonicalLinks
import Hypertournaments.OddToggleP1Core

/-!
# The exact finite support of differences between the p1 link tables

The two canonical links agree on every old pair involving a pad.
On a core-core pair they differ exactly along the seven eligible
edges of the certified six-vertex graph. This is the intrinsic
source-table support condition used later to rule out homogeneous
mixed packets in any hypothetical joint extension.
-/

namespace Hypertournaments

/-- Exact six-core eligibility for canonical link disagreement,
including reversed and diagonal pairs. -/
theorem p1CoreSym_disagree_iff_eligible :
    ∀ i j : Fin 6,
      (p1CoreLeftSymBit i j ≠ p1CoreRightSymBit i j) ↔
        p1CoreEligible i j := by
  decide

/-- Any difference between actual canonical left and right p1
links must lie on an eligible pair of core vertices. -/
theorem p1CanonicalLink_disagreement_support
    (k : ℕ) (v w : Fin (4*k+6))
    (h : p1CanonicalLink k true v w ≠
      p1CanonicalLink k false v w) :
    ∃ i j : Fin 6, v = p1CoreAt k i ∧
      w = p1CoreAt k j ∧ p1CoreEligible i j := by
  rcases p1OldVertex_pad_or_core k v with ⟨s, hs⟩ | ⟨i, hi⟩
  · have hp : v.val < 4*k := by
      rw [← hs]
      exact p1PadAt_lt k s
    exact False.elim
      (h (p1CanonicalLink_pad_agree k v w (Or.inl hp)))
  · rcases p1OldVertex_pad_or_core k w with ⟨t, ht⟩ | ⟨j, hj⟩
    · have hp : w.val < 4*k := by
        rw [← ht]
        exact p1PadAt_lt k t
      exact False.elim
        (h (p1CanonicalLink_pad_agree k v w (Or.inr hp)))
    · refine ⟨i, j, hi.symm, hj.symm, ?_⟩
      rw [← hi, ← hj,
        p1CanonicalLink_core_left, p1CanonicalLink_core_right] at h
      exact (p1CoreSym_disagree_iff_eligible i j).mp h

/-- Conversely, every eligible core pair has opposite canonical
link bits. -/
theorem p1CanonicalLink_disagreement_of_eligible
    (k : ℕ) (i j : Fin 6)
    (h : p1CoreEligible i j) :
    p1CanonicalLink k true (p1CoreAt k i) (p1CoreAt k j) ≠
      p1CanonicalLink k false (p1CoreAt k i) (p1CoreAt k j) := by
  rw [p1CanonicalLink_core_left, p1CanonicalLink_core_right]
  exact (p1CoreSym_disagree_iff_eligible i j).mpr h

end Hypertournaments
