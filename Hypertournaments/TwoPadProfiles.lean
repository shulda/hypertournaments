import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
import Hypertournaments.NegativeReduction

/-!
# Finite-profile pigeonhole lemma for two-coordinate reflection

In the suspension/reflection argument, each auxiliary padding vertex
records a Boolean profile on a finite collection of old (n-1)-sets.
Once the number of pads exceeds the number of profiles, two distinct
pads have exactly the same profile.  We strengthen the conclusion
to an ordered pair p<q, which the alternating packet computation needs.

This is just the combinatorial entry point for two-coordinate
reflection, not the arity-transfer theorem itself.
-/

namespace Hypertournaments

/-- There are at most 2^(card I) Boolean profiles on a finite index
type I. Hence more padding vertices than profiles produce an ordered
pair with equal profile. -/
theorem repeatedBoolProfile
    {I : Type*} [Fintype I]
    (p : ℕ) (hp : 2 ^ Fintype.card I < p)
    (profile : Fin p → I → Bool) :
    ∃ x y : Fin p, x < y ∧ profile x = profile y := by
  classical
  by_contra h
  have hinj : Function.Injective profile := by
    intro x y heq
    by_contra hne
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact h ⟨x, y, hxy, heq⟩
    · exact hne hxy
    · exact h ⟨y, x, hxy, heq.symm⟩
  have hcard : p ≤ 2 ^ Fintype.card I := by
    simpa using Fintype.card_le_of_injective profile hinj
  omega

end Hypertournaments
