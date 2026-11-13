import Mathlib.Algebra.BigOperators.Ring.Finset
import Hypertournaments.OddToggleP3FiniteUnionBound

/-!
# Exact denominator-free finite union bound for p3 gauge events

The earlier finite union bound used a common *integer* upper bound
on each bad-event cardinality. For the p3 construction the natural
statement is instead a fraction such as
    P * |bad_i| <= Q * |sample|
where P,Q are the exact full-trial numerator/denominator from the
independent Boolean source count, uniformly over gauge i.

When |gauges| * Q < P and the sample space is nonempty, these
cardinality inequalities imply that the union of all bad gauge
events cannot cover the finite sample space. There is no division
by cardinalities and no probability-measure axiom.
-/

namespace Hypertournaments

/-- A uniform *rational* event-size bound, represented as a
natural-number cross multiplication, suffices for the finite
gauge union bound. The strict inequality on the numerator and
denominator excludes the union of all bad events. -/
theorem p3FiniteUnionBound_of_fraction_bound
    {Ω I : Type*} [DecidableEq Ω]
    (sample : Finset Ω) (gauges : Finset I)
    (bad : I → Finset Ω)
    (P Q : ℕ)
    (hSample : 0 < sample.card)
    (hsub : ∀ i ∈ gauges, bad i ⊆ sample)
    (hRatio : ∀ i ∈ gauges,
      P * (bad i).card ≤ Q * sample.card)
    (hSmall : gauges.card * Q < P) :
    ∃ x ∈ sample, ∀ i ∈ gauges, x ∉ bad i := by
  classical
  have hscaled :
      P * (∑ i ∈ gauges, (bad i).card) ≤
        (gauges.card * Q) * sample.card := by
    calc
      P * (∑ i ∈ gauges, (bad i).card) =
          ∑ i ∈ gauges, P * (bad i).card := by
            simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ gauges, Q * sample.card := by
          apply Finset.sum_le_sum
          intro i hi
          exact hRatio i hi
      _ = (gauges.card * Q) * sample.card := by
          simp [mul_assoc]
  have hstrict : (∑ i ∈ gauges, (bad i).card) < sample.card := by
    by_contra hnot
    have hle : sample.card ≤ (∑ i ∈ gauges, (bad i).card) :=
      Nat.le_of_not_gt hnot
    have hscaledLow :
        P * sample.card ≤ P * (∑ i ∈ gauges, (bad i).card) :=
      Nat.mul_le_mul_left P hle
    have htooLarge :
        P * sample.card ≤ (gauges.card * Q) * sample.card :=
      hscaledLow.trans hscaled
    have hlt :
        (gauges.card * Q) * sample.card < P * sample.card :=
      mul_lt_mul_of_pos_right hSmall hSample
    exact (not_le_of_gt hlt) htooLarge
  exact p3FiniteUnionBound_exists_good sample gauges bad hsub hstrict

end Hypertournaments
