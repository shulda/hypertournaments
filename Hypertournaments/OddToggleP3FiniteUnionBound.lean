import Hypertournaments.Basic

/-!
# Exact finite union bound for the p3 random non-amalgamation witness

The p3 proof chooses one finite uniformly random assignment of
potential bits and considers one bad event for each possible gauge.
If the sum of the cardinalities of these bad events is smaller than
the entire sample space, at least one assignment avoids all gauges.

These pure finite-set lemmas state this counting step without
probability measures or asymptotic estimates. A further convenient
form assumes a common cardinal bound C on each event: if
  (#gauges) * C < (#sample assignments)
then a gauge-avoiding assignment exists.

The random p3 construction still needs to instantiate the events,
the exact per-gauge C from independent transversals, and the
strict numerical witness inequality.
-/

namespace Hypertournaments

/-- If the union-bound sum is smaller than the finite ambient
sample space, some sample avoids ALL selected bad events. -/
theorem p3FiniteUnionBound_exists_good
    {Ω I : Type*} [DecidableEq Ω]
    (sample : Finset Ω) (gauges : Finset I)
    (bad : I → Finset Ω)
    (hsub : ∀ i ∈ gauges, bad i ⊆ sample)
    (hsmall : (∑ i ∈ gauges, (bad i).card) < sample.card) :
    ∃ x ∈ sample, ∀ i ∈ gauges, x ∉ bad i := by
  classical
  let unionBad : Finset Ω := gauges.biUnion bad
  have hsubset : unionBad ⊆ sample := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hsub i hi hxi
  have hcard : unionBad.card ≤ ∑ i ∈ gauges, (bad i).card := by
    exact Finset.card_biUnion_le
  have hlt : unionBad.card < sample.card :=
    lt_of_le_of_lt hcard hsmall
  by_contra hNo
  have hreverse : sample ⊆ unionBad := by
    intro x hx
    by_contra hnot
    apply hNo
    refine ⟨x, hx, ?_⟩
    intro i hi hxi
    exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩)
  have heq : unionBad = sample :=
    Finset.Subset.antisymm hsubset hreverse
  rw [heq] at hlt
  exact (lt_irrefl _) hlt

/-- The finite gauge-union bound with one common per-gauge
event-size upper bound. -/
theorem p3FiniteUnionBound_of_common_event_bound
    {Ω I : Type*} [DecidableEq Ω]
    (sample : Finset Ω) (gauges : Finset I)
    (bad : I → Finset Ω) (C : ℕ)
    (hsub : ∀ i ∈ gauges, bad i ⊆ sample)
    (hevent : ∀ i ∈ gauges, (bad i).card ≤ C)
    (hsmall : gauges.card * C < sample.card) :
    ∃ x ∈ sample, ∀ i ∈ gauges, x ∉ bad i := by
  have hsum : (∑ i ∈ gauges, (bad i).card) ≤ gauges.card * C := by
    calc
      (∑ i ∈ gauges, (bad i).card) ≤ ∑ _i ∈ gauges, C := by
        apply Finset.sum_le_sum
        intro i hi
        exact hevent i hi
      _ = gauges.card * C := by simp
  exact p3FiniteUnionBound_exists_good
    sample gauges bad hsub (lt_of_le_of_lt hsum hsmall)

end Hypertournaments
