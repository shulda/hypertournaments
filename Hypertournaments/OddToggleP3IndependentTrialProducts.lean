import Hypertournaments.OddToggleP3BadPatternCount

/-!
# Product counting for independent p3 trial patterns

A selected zero-sum transversal uses m independent link bits
and one independent full-transversal W bit. For any fixed gauge
and deterministic side data, the two phase-dependent alternating
patterns are exactly the bad patterns among the 2^(m+1)
possible Boolean words.

For ANY finite family T of independent trials, with potentially
different bad-endpoint choice functions at each trial, the type
of simultaneous GOOD per-trial assignments has EXACT cardinal
  (2^(m+1)-2)^|T|.

This is the finite product-counting form of independence,
prior to mapping actual W,L,R potential sources to these trial
coordinates. No measure theory or AP claim is made here.
-/

namespace Hypertournaments

/-- A selected trial's finite set of bad Boolean assignments. -/
def p3TrialBadPatterns (m : ℕ) (choice : Bool → Bool) :
    Finset ((Fin m ⊕ Unit) → Bool) :=
  (Finset.univ : Finset Bool).image (p3BadPattern m choice)

/-- Every trial has exactly two bad patterns when m>0. -/
theorem p3TrialBadPatterns_card (m : ℕ) (hm : 0 < m)
    (choice : Bool → Bool) :
    (p3TrialBadPatterns m choice).card = 2 :=
  p3BadPattern_exact_two m hm choice

/-- An independent trial has exactly 2^(m+1)-2 GOOD full
interior-plus-endpoint Boolean assignments, uniformly in the
choice of phase-dependent forbidden endpoint. -/
theorem p3TrialGoodPatterns_card
    (m : ℕ) (hm : 0 < m) (choice : Bool → Bool) :
    Fintype.card
      {bits : (Fin m ⊕ Unit) → Bool //
        bits ∉ p3TrialBadPatterns m choice} =
      2^(m+1) - 2 := by
  classical
  let A := (Fin m ⊕ Unit) → Bool
  let P := p3TrialBadPatterns m choice
  have hbad :
      Fintype.card {bits : A // bits ∈ P} = P.card := by
    rw [Fintype.card_subtype]
    simp
  have hcompl :=
    Fintype.card_subtype_compl (fun bits : A => bits ∈ P)
  change Fintype.card {bits : A // bits ∉ P} =
    Fintype.card A - Fintype.card {bits : A // bits ∈ P} at hcompl
  rw [hcompl, p3BadPattern_total_card m, hbad,
    p3TrialBadPatterns_card m hm choice]

/-- Exact number of independent good choices on a finite family
of trials: a product of equally sized good-pattern factors. -/
theorem p3IndependentGoodTrialAssignments_card
    (m : ℕ) (hm : 0 < m)
    {T : Type*} [Fintype T]
    (choice : T → Bool → Bool) :
    Fintype.card
      (∀ t : T,
        {bits : (Fin m ⊕ Unit) → Bool //
          bits ∉ p3TrialBadPatterns m (choice t)}) =
      (2^(m+1)-2)^(Fintype.card T) := by
  classical
  calc
    Fintype.card
      (∀ t : T, {bits : (Fin m ⊕ Unit) → Bool //
        bits ∉ p3TrialBadPatterns m (choice t)}) =
        ∏ t : T,
          Fintype.card {bits : (Fin m ⊕ Unit) → Bool //
            bits ∉ p3TrialBadPatterns m (choice t)} :=
      Fintype.card_pi
    _ = ∏ _t : T, (2^(m+1)-2) := by
      apply Finset.prod_congr rfl
      intro t _
      exact p3TrialGoodPatterns_card m hm (choice t)
    _ = (2^(m+1)-2)^(Fintype.card T) := by simp

end Hypertournaments
