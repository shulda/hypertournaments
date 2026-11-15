import Lean.Elab.Tactic.Omega
import Hypertournaments.RootedOddOnePointWitness
import Hypertournaments.NegativeReduction
import Hypertournaments.SeedFourBadOnePoint

/-!
# Odd-arity negative one-point induction outside the switching exception

The concrete rooted odd suspension upgrades a lower bad ordinary
one-point witness from arity 2k+1 to arity 2k+3 whenever the shifted
higher type family is itself a non-switching negative lower family.

The remaining exceptional case is precisely
  shiftedAllowed T = switchingAllowed (2k+1).
It is NOT covered by this lemma and requires independent analysis.
-/

namespace Hypertournaments

/-- Nonexceptional inductive negative direction from every odd arity
at least five to the next odd arity, with explicit bad ordinary
one-point witnesses rather than an abstract failure of AP. -/
theorem negativeOnePointGoal_odd_nonexceptional_step
    (k : ℕ) (hk : 2 ≤ k)
    (hind : NegativeOnePointGoal (2*k+1))
    (T : Set ℕ)
    (hvalid : ValidTypes (2*k+3) T)
    (hcentral : centralIndex (2*k+3) ∈ T)
    (hmissing : nextCentralIndex (2*k+3) ∉ T)
    (hnon : shiftedAllowed T ≠ switchingAllowed (2*k+1)) :
    HasBadOnePoint (2*k+3) T := by
  have hn : 4 ≤ 2*k+1 := by omega
  have hv : ValidTypes (2*k+1) (shiftedAllowed T) :=
    shiftedAllowed_valid (2*k+1) T hvalid
  have hc : centralIndex (2*k+1) ∈ shiftedAllowed T :=
    shiftedAllowed_central (2*k+1) T hcentral
  have hm : nextCentralIndex (2*k+1) ∉ shiftedAllowed T :=
    shiftedAllowed_next_missing (2*k+1) T hn hmissing
  have hbad : HasBadOnePoint (2*k+1) (shiftedAllowed T) :=
    hind (shiftedAllowed T) hv hc hm (Or.inr hnon)
  have hkcentral : k+1 ∈ shiftedAllowed T := by
    have heq : centralIndex (2*k+1) = k+1 := by
      unfold centralIndex
      omega
    rw [heq] at hc
    exact hc
  exact HasBadOnePoint.oddRootedSuspension
    k (by omega) (shiftedAllowed T) T hkcentral
    (by intro d hd; exact hd) (Set.Subset.rfl) hbad

end Hypertournaments
