import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Hypertournaments.OddToggleP3BoolPhases

/-!
# Exact 2-of-2^(m+1) bad endpoint-interior patterns for p3

The p3 mixed packet obstruction is determined by m independent
interior potential bits and one independent base potential bit.
For any fixed gauge and fixed side data, the interior must be one
of the two alternating Boolean phase words. For each phase, the
unique forbidden base bit is a deterministic Bool value.

We encode this as a family p3BadPattern indexed by the two
alternating phases. Its interior coordinates are alternating and
its final coordinate is the uniquely forbidden base bit chosen by
an ARBITRARY function choice : Bool → Bool.

For m>0 the two bad patterns are distinct, so there are EXACTLY
two bad patterns among the 2^(m+1) Boolean assignments. The
ratio is 2^(-m), the per-transversal probability claimed in
the mathematical argument. This module proves only the finite
numerator/denominator counts, not a probability measure or AP.
-/

namespace Hypertournaments

/-- Two-phase alternating interior and phase-dependent unique
forbidden independent endpoint bit. The input coordinate space
is Fin m ⊕ Unit, i.e. exactly m+1 independent Boolean bits. -/
def p3BadPattern (m : ℕ)
    (choice : Bool → Bool) (phase : Bool) :
    (Fin m ⊕ Unit) → Bool :=
  fun s => match s with
    | Sum.inl i => p3AlternatingWord m phase i
    | Sum.inr _ => choice phase

/-- The two bad phase patterns are different whenever the
alternating interior contains at least one coordinate. -/
theorem p3BadPattern_injective
    (m : ℕ) (hm : 0 < m) (choice : Bool → Bool) :
    Function.Injective (p3BadPattern m choice) := by
  intro p q hpq
  have hinner :
      p3AlternatingWord m p = p3AlternatingWord m q := by
    funext i
    have hi := congrFun hpq (Sum.inl i)
    exact hi
  exact p3AlternatingWord_injective m hm hinner

/-- Exactly two (and not more) independent-bit words have
alternating interior and their prescribed unique bad endpoint. -/
theorem p3BadPattern_exact_two
    (m : ℕ) (hm : 0 < m) (choice : Bool → Bool) :
    ((Finset.univ : Finset Bool).image
      (p3BadPattern m choice)).card = 2 := by
  classical
  rw [Finset.card_image_of_injective _
    (p3BadPattern_injective m hm choice)]
  decide

/-- The full sample space of m interior bits and one base bit
contains exactly 2^(m+1) distinct Boolean patterns. -/
theorem p3BadPattern_total_card (m : ℕ) :
    Fintype.card ((Fin m ⊕ Unit) → Bool) = 2^(m+1) := by
  classical
  simp [Fintype.card_sum]

end Hypertournaments
