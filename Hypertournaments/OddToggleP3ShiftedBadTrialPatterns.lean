import Hypertournaments.OddToggleP3AllTrialsCount

/-!
# Gauge-shifted forbidden p3 trial patterns

The real mixed facet word is the independent raw link word XOR
a deterministic gauge shift. Therefore the two forbidden SOURCE
patterns for a fixed gauge are shifted alternating words, not
necessarily alternating source words themselves.

We correct the probability-to-geometry interface: shifting
the m link coordinates is an involutive equivalence that fixes
the separate independent W coordinate. Consequently, for EVERY
fixed shift and phase-dependent bad W prescription, exactly
two full local source words are forbidden and precisely
2^(m+1)-2 remain. This is an exact finite count, not a heuristic.
-/

namespace Hypertournaments

/-- XOR a deterministic shift into the link coordinates of
one full trial source word, leaving its independent W bit fixed. -/
def p3ShiftTrialWord (m : ℕ) (shift : Fin m → Bool)
    (w : p3TrialPatternWord m) : p3TrialPatternWord m
  | Sum.inl i => w (Sum.inl i) ^^ shift i
  | Sum.inr u => w (Sum.inr u)

/-- Shifting a full source trial word twice recovers that word. -/
theorem p3ShiftTrialWord_involutive (m : ℕ)
    (shift : Fin m → Bool) :
    Function.Involutive (p3ShiftTrialWord m shift) := by
  intro w
  funext x
  cases x with
  | inl i =>
      change ((w (Sum.inl i) ^^ shift i) ^^ shift i) =
        w (Sum.inl i)
      cases (w (Sum.inl i)) <;> cases (shift i) <;> decide
  | inr u =>
      cases u
      rfl

/-- Two actual raw-link source patterns which produce an
alternating mixed interior after the fixed gauge shift. -/
def p3ShiftedBadTrialPattern (m : ℕ)
    (shift : Fin m → Bool) (choice : Bool → Bool)
    (phase : Bool) : p3TrialPatternWord m :=
  p3ShiftTrialWord m shift (p3BadPattern m choice phase)

def p3ShiftedBadTrialPatternSet (m : ℕ)
    (shift : Fin m → Bool) (choice : Bool → Bool) :
    Finset (p3TrialPatternWord m) :=
  (Finset.univ : Finset Bool).image
    (p3ShiftedBadTrialPattern m shift choice)

/-- The two shifted bad phase-patterns are distinct. -/
theorem p3ShiftedBadTrialPattern_injective
    (m : ℕ) (hm : 0 < m)
    (shift : Fin m → Bool) (choice : Bool → Bool) :
    Function.Injective
      (p3ShiftedBadTrialPattern m shift choice) := by
  intro p q hpq
  apply p3BadPattern_injective m hm choice
  have h := congrArg (p3ShiftTrialWord m shift) hpq
  change
    p3ShiftTrialWord m shift
      (p3ShiftTrialWord m shift (p3BadPattern m choice p)) =
    p3ShiftTrialWord m shift
      (p3ShiftTrialWord m shift (p3BadPattern m choice q)) at h
  rw [p3ShiftTrialWord_involutive m shift,
    p3ShiftTrialWord_involutive m shift] at h
  exact h

/-- Exactly TWO local source words are forbidden, for every
fixed link gauge shift and phase-dependent W prescription. -/
theorem p3ShiftedBadTrialPatternSet_card
    (m : ℕ) (hm : 0 < m)
    (shift : Fin m → Bool) (choice : Bool → Bool) :
    (p3ShiftedBadTrialPatternSet m shift choice).card = 2 := by
  classical
  unfold p3ShiftedBadTrialPatternSet
  rw [Finset.card_image_of_injective _
    (p3ShiftedBadTrialPattern_injective m hm shift choice)]
  decide

/-- The exact good-word count is unchanged by an arbitrary
fixed Boolean shift of the interior source coordinates. -/
theorem p3ShiftedGoodTrialPatterns_card
    (m : ℕ) (hm : 0 < m)
    (shift : Fin m → Bool) (choice : Bool → Bool) :
    Fintype.card
      {word : p3TrialPatternWord m //
        word ∉ p3ShiftedBadTrialPatternSet m shift choice} =
      2^(m+1)-2 := by
  classical
  have hbad :
      Fintype.card
        {word : p3TrialPatternWord m //
          word ∈ p3ShiftedBadTrialPatternSet m shift choice} = 2 := by
    calc
      _ = (p3ShiftedBadTrialPatternSet m shift choice).card :=
        Fintype.subtype_card
          (p3ShiftedBadTrialPatternSet m shift choice)
          (by intro word; rfl)
      _ = 2 :=
        p3ShiftedBadTrialPatternSet_card m hm shift choice
  have hcompl := Fintype.card_subtype_compl
    (fun word : p3TrialPatternWord m =>
      word ∈ p3ShiftedBadTrialPatternSet m shift choice)
  have htotal : Fintype.card (p3TrialPatternWord m) =
      2^(m+1) := p3BadPattern_total_card m
  simpa only [hbad, htotal] using hcompl

end Hypertournaments
