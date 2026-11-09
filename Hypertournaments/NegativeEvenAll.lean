import Hypertournaments.SeedFourBadOnePoint
import Hypertournaments.NegativeReduction

/-!
# Unconditional negative classification in every even arity

The ordinary AP obstruction in even arities can be proved by
induction on genuine bad one-point diagrams. The arity-four
central-containing negative seed already has such witnesses, and
the concrete even two-coordinate suspension preserves them.

This avoids assuming that arbitrary failure of AP has
a one-point witness. Induction propagates a witness, rather than
trying to reconstruct a witness from a mere negation of AP.

As a result we prove the complete *even-arity necessary direction*:
for every even n>=4 and a valid allowed type set S containing the
central local type, ordinary AP forces the next-to-central type
to be present. The positive direction and all odd arities are
separate.
-/

namespace Hypertournaments

/-- A strong negative witness in even arity n=2k propagates to
n+2 for every valid central-containing target omitting the
next-to-central type. -/
theorem negativeOnePointGoal_even_step
    (k : ℕ) (hk : 2 ≤ k)
    (hind : NegativeOnePointGoal (2*k)) :
    NegativeOnePointGoal (2*k+2) := by
  intro T hvalid hcentral hmissing _
  have hn : 4 ≤ 2*k := by omega
  have hlowValid := shiftedAllowed_valid (2*k) T hvalid
  have hlowCentral := shiftedAllowed_central (2*k) T hcentral
  have hlowMissing :=
    shiftedAllowed_next_missing (2*k) T hn hmissing
  have hlowEven : Even (2*k) := ⟨k, by omega⟩
  have hlowWitness :
      HasBadOnePoint (2*k) (shiftedAllowed T) :=
    hind (shiftedAllowed T) hlowValid hlowCentral
      hlowMissing (Or.inl hlowEven)
  have hkcenter : k ∈ shiftedAllowed T := by
    have hcenter : centralIndex (2*k) = k := by
      unfold centralIndex
      omega
    rw [hcenter] at hlowCentral
    exact hlowCentral
  have hraise :
      ∀ d : ℕ, d ∈ shiftedAllowed T → d+1 ∈ T := by
    intro d hd
    exact hd
  exact HasBadOnePoint.evenSuspension
    k (shiftedAllowed T) T hkcenter
    hraise (Set.Subset.rfl) hlowWitness

/-- Every negative central-containing type family in every
even arity n>=4 has an explicit bad ordinary one-point span. -/
theorem negativeOnePointGoal_even_all
    (n : ℕ) (hn : 4 ≤ n) (he : Even n) :
    NegativeOnePointGoal n := by
  obtain ⟨k, hk⟩ := he
  have hn2 : n = 2*k := by omega
  have hk2 : 2 ≤ k := by omega
  subst n
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j+2 :=
    ⟨k-2, by omega⟩
  subst k
  have hall : ∀ j : ℕ, NegativeOnePointGoal (2*(j+2)) := by
    intro j
    induction j with
    | zero =>
        simpa using seedFour_negativeOnePointGoal
    | succ j ih =>
        have hstep :=
          negativeOnePointGoal_even_step (j+2) (by omega) ih
        have heq :
            2 * (Nat.succ j + 2) = 2 * (j+2) + 2 := by omega
        rw [heq]
        exact hstep
  simpa only [two_mul] using hall j

/-- UNCONDITIONAL complete negative classification for every even
arity at least four, using ordinary AP and actual local types. -/
theorem negative_classification_even_all
    (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    nextCentralIndex n ∈ S := by
  by_contra hmissing
  have hbad : HasBadOnePoint n S :=
    (negativeOnePointGoal_even_all n hn he)
      S hvalid hcentral hmissing (Or.inl he)
  exact (not_hasAP_of_bad_onePoint hbad) hAP

end Hypertournaments
