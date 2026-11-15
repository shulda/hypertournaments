import Mathlib.SetTheory.Cardinal.Finite
import Hypertournaments.OddToggleP3FiniteBadEventCount
import Hypertournaments.OddToggleP3BadPatternCount

/-!
# Exactly a 2^(-m) fraction of globally assigned bits are bad per trial

For each selected zero-sum transversal, there are m interior source
bits and one independent base W bit. For any fixed gauge and all
other deterministic side data, the two alternating interior phases
each prescribe exactly one forbidden W value. The verified finite
p3BadPattern count shows there are precisely two forbidden patterns
among 2^(m+1) possible interior/base assignments, for m>0.

If these m+1 selected coordinates are injected into any finite
global potential bit index set B, the uniform finite source
restriction theorem gives the EXACT integer frequency equation
  2^(m+1) * |bad global assignments| = 2 * 2^|B|.

This proves the finite cardinal counterpart of per-trial bad
probability 2^(-m); NO probability measure or ordinary AP conclusion
is asserted. Independence between many transversals and the
finite gauge union bound remain separate applications.
-/

namespace Hypertournaments

/-- Every fixed bad-endpoint choice function gives exactly a
2^(-m) fraction of global Boolean source assignments causing
the selected trial to have an alternating interior AND its
uniquely forbidden base endpoint. The equation uses only Nat.card. -/
theorem p3BadTrial_exact_finite_frequency
    (m : ℕ) (hm : 0 < m)
    {B : Type*} [Fintype B]
    (f : (Fin m ⊕ Unit) → B) (hf : Function.Injective f)
    (choice : Bool → Bool) :
    2 ^ (m+1) *
      Nat.card
        {values : B → Bool //
          (fun s : Fin m ⊕ Unit => values (f s)) ∈
            ((Finset.univ : Finset Bool).image
              (p3BadPattern m choice))} =
    2 * 2 ^ (Fintype.card B) := by
  classical
  let P : Finset ((Fin m ⊕ Unit) → Bool) :=
    (Finset.univ : Finset Bool).image (p3BadPattern m choice)
  have hP : P.card = 2 :=
    p3BadPattern_exact_two m hm choice
  have hA : Fintype.card (Fin m ⊕ Unit) = m+1 := by simp
  have h :=
    p3BoolRestriction_badEvent_exact_ratio
      f hf P (p3BadPattern m choice false)
  rw [hA, hP] at h
  simpa only [P] using h

end Hypertournaments
