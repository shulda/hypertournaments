import Hypertournaments.OddToggleP3GlobalAllTrialsExact
import Hypertournaments.OddToggleP3FullSourceWitnessHalf

/-!
# Strict full global source event-cardinality bound per fixed p3 gauge

For every finite abelian block group G of the exact selected witness
size t, the global Boolean W/link assignment experiment has a
precisely known number of assignments avoiding all selected forbidden
trial patterns for ANY fixed trial-by-trial phase-to-endpoint choice.

The full source counting theorem gives the exact integer ratio
 P * |good assignments| = Q * |all assignments|,
with
 P=2^((m+1)*t^(m-1)),
 Q=(2^(m+1)-2)^(t^(m-1)).
The independently proved explicit witness inequality bounds
  2^(D+1) * Q < P
with D=choose(m*t,m-2). We multiply the first equality by the
number of gauges, compare both sides in Nat, and cancel the positive
factor P without division. Thus even 2^D fixed gauge options have
total bound strictly below one half of all assignments.

This is a numeric/event-cardinality theorem ONLY. It does not yet
identify these symbolic patterns with the actual mixed facet packet
of an arbitrary hypothetical intrinsic amalgam.
-/

namespace Hypertournaments

/-- Exact strict per-gauge cardinal inequality, for the complete
global W/link Boolean source experiment and explicit block size. -/
theorem p3Witness_globalGoodGauge_strict_half
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m : ℕ) (hm : 2 ≤ m)
    (hCard : Fintype.card G = p3WitnessBlockSize m)
    (choice : p3SelectedTrials G (m-1) → Bool → Bool) :
    2 ^ (((m*p3WitnessBlockSize m).choose (m-2)) + 1) *
      Nat.card {values : p3FullSourceSpace G (m-1) → Bool //
        (fun qi : p3FullSelectedSpace G (m-1) =>
          values (p3FullTrialSourceIndex (m-1) qi)) ∈
          p3GoodSelectedTrialSet (m-1) choice} <
      2 ^ (Fintype.card (p3FullSourceSpace G (m-1))) := by
  let s : ℕ := m-1
  let t : ℕ := p3WitnessBlockSize m
  let N : ℕ := t^s
  let P : ℕ := 2^((m+1)*N)
  let Q : ℕ := (2^(m+1)-2)^N
  let K : ℕ := 2^(((m*t).choose (m-2))+1)
  let Good : ℕ :=
    Nat.card {values : p3FullSourceSpace G s → Bool //
      (fun qi : p3FullSelectedSpace G s =>
        values (p3FullTrialSourceIndex s qi)) ∈
        p3GoodSelectedTrialSet s choice}
  let Total : ℕ := 2^(Fintype.card (p3FullSourceSpace G s))
  have hsize : s+2 = m+1 := by dsimp [s]; omega
  have hRatio : P*Good = Q*Total := by
    have hr := p3AllGlobalGoodTrialAssignments_exact_ratio
      (G:=G) s choice
    rw [hsize, hCard] at hr
    exact hr
  have hNumeric : K*Q < P := by
    have hh := p3Witness_fullSourceGauge_strict_half m hm
    change K*Q < P at hh
    exact hh
  have hTotal : 0 < Total := by dsimp [Total]; positivity
  have hscaled : (K*Good)*P < Total*P := by
    calc
      (K*Good)*P = K*(P*Good) := by ring
      _ = K*(Q*Total) := by rw [hRatio]
      _ = (K*Q)*Total := by ring
      _ < P*Total := mul_lt_mul_of_pos_right hNumeric hTotal
      _ = Total*P := by ring
  change K*Good < Total
  by_contra hnot
  have hle : Total ≤ K*Good := Nat.le_of_not_gt hnot
  have hcontr : Total*P ≤ (K*Good)*P :=
    Nat.mul_le_mul_right P hle
  exact (not_le_of_gt hscaled) hcontr

end Hypertournaments
