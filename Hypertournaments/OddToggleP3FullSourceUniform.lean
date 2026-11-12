import Hypertournaments.OddToggleP3FullTrialSources
import Hypertournaments.OddToggleP3FiniteBadEventCount

/-!
# Exact finite uniformity of all p3 full-trial W/link sources

For each zero-sum transversal q, the combined source map indexes
all its punctured link variables and one independent full W(q) bit.
The already proved full-trial injection makes arbitrary assignments
of these selected bits extend to a single global Boolean potential
assignment. The same map gives an exact finite uniform-fiber identity
and a cardinal frequency formula for ANY prescribed finite set
of selected bit words.

This removes the discrepancy between link-only and full W/link
source counting. The event-specific restrictions, side admissibility,
joint packets, and ordinary non-AP are still independent obligations.
-/

namespace Hypertournaments

/-- The full ambient index type contains punctured link-variable
sources in the left summand and full W-transversal sources in the
right summand. -/
abbrev p3FullSourceSpace (G : Type*) (s : ℕ) :=
  (Fin (s+1) × (Fin (s+1) → G)) ⊕ (Fin (s+1) → G)

/-- The finite zero-sum code with one selected input coordinate for
each link bit and a separate selected input for the base W bit. -/
abbrev p3FullSelectedSpace (G : Type*) [AddCommGroup G] (s : ℕ) :=
  {q : Fin (s+1) → G // (∑ i : Fin (s+1), q i) = 0} ×
    (Fin (s+1) ⊕ Unit)

/-- Every Boolean word on ALL selected W and link sources is the
restriction of some global assignment. No trial source is reused. -/
theorem p3FullTrialRestriction_surjective
    {G : Type*} [AddCommGroup G] (s : ℕ) :
    Function.Surjective
      (fun values : p3FullSourceSpace G s → Bool =>
        fun qi : p3FullSelectedSpace G s =>
          values (p3FullTrialSourceIndex s qi)) := by
  exact p3BoolRestriction_surjective
    (p3FullTrialSourceIndex (G:=G) s)
    (p3FullTrialSourceIndex_injective (G:=G) s)

/-- Every full selected trial-bit prescription has exactly
the same finite number of global W/link extensions, with
2^((s+2)*|G|^s) equally likely selected words. -/
theorem p3FullTrialRestriction_exact_fiber_count
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (target : p3FullSelectedSpace G s → Bool) :
    2 ^ (Fintype.card (p3FullSourceSpace G s)) =
      2 ^ ((s+2) * (Fintype.card G)^s) *
        Nat.card {values : p3FullSourceSpace G s → Bool //
          (fun qi : p3FullSelectedSpace G s =>
             values (p3FullTrialSourceIndex s qi)) = target} := by
  have h := p3BoolRestriction_exact_fiber_count
    (p3FullTrialSourceIndex (G:=G) s)
    (p3FullTrialSourceIndex_injective (G:=G) s)
    target
  rw [p3FullTrialSourceIndex_card (G:=G) s] at h
  exact h

/-- The selected full W/link bit pattern family has precisely
P.card / 2^((s+2)*|G|^s) of all global Boolean assignments,
expressed as an exact natural-number equation. -/
theorem p3FullTrialRestriction_exact_pattern_ratio
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (P : Finset (p3FullSelectedSpace G s → Bool)) :
    2 ^ ((s+2) * (Fintype.card G)^s) *
      Nat.card {values : p3FullSourceSpace G s → Bool //
        (fun qi : p3FullSelectedSpace G s =>
           values (p3FullTrialSourceIndex s qi)) ∈ P} =
      P.card * 2 ^ (Fintype.card (p3FullSourceSpace G s)) := by
  have h := p3BoolRestriction_badEvent_exact_ratio
    (p3FullTrialSourceIndex (G:=G) s)
    (p3FullTrialSourceIndex_injective (G:=G) s)
    P (fun _ => false)
  rw [p3FullTrialSourceIndex_card (G:=G) s] at h
  exact h

end Hypertournaments
