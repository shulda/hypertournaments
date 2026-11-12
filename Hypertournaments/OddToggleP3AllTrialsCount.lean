import Hypertournaments.OddToggleP3BadPatternCount

/-!
# Exact all-trials finite product count for the p3 random obstruction

For each selected transversal trial, an m-bit interior vector plus
one independent base bit is a word on Fin m ⊕ Unit. Two words are
forbidden, even when the identity of these words depends arbitrarily
on the trial. Every remaining word is admissible.

Here the independent random coordinates are represented as the
finite product T → ((Fin m ⊕ Unit) → Bool). We prove that the set
of assignments avoiding every forbidden trial has cardinality
(2^(m+1)-2)^|T|, *uniformly in the choice of bad patterns*.
This is the exact finite counting analogue of multiplying
independent per-trial avoidance probabilities.

The separate injective source-index and restriction lemmas must
still transfer this result to the actual global W/L/R potential
assignments. No ordinary AP claim is made.
-/

namespace Hypertournaments

/-- One trial consists of m link bits and one separate W bit. -/
abbrev p3TrialPatternWord (m : ℕ) := (Fin m ⊕ Unit) → Bool

/-- For a specified phase-dependent bad endpoint bit there are
exactly two bad full-trial patterns. -/
def p3BadTrialPatternSet (m : ℕ) (choice : Bool → Bool) :
    Finset (p3TrialPatternWord m) :=
  (Finset.univ : Finset Bool).image (p3BadPattern m choice)

/-- Exactly 2^(m+1)-2 complete local assignments avoid both forbidden
p3 patterns, independently of how the bad W bit depends on the phase. -/
theorem p3GoodTrialPatterns_card
    (m : ℕ) (hm : 0 < m) (choice : Bool → Bool) :
    Fintype.card
      {word : p3TrialPatternWord m //
        word ∉ p3BadTrialPatternSet m choice} =
      2^(m+1)-2 := by
  classical
  have hbad :
      Fintype.card
        {word : p3TrialPatternWord m //
          word ∈ p3BadTrialPatternSet m choice} = 2 := by
    calc
      _ = (p3BadTrialPatternSet m choice).card :=
        Fintype.subtype_card
          (p3BadTrialPatternSet m choice) (by intro word; rfl)
      _ = 2 := p3BadPattern_exact_two m hm choice
  have hcompl := Fintype.card_subtype_compl
    (fun word : p3TrialPatternWord m =>
      word ∈ p3BadTrialPatternSet m choice)
  have htotal : Fintype.card (p3TrialPatternWord m) =
      2^(m+1) := p3BadPattern_total_card m
  simpa only [hbad, htotal] using hcompl

/-- Independent trial assignments avoiding all their respective
bad patterns are equivalent to a dependent product of locally
admissible words. The forbidden choice may vary with the trial. -/
def p3GoodTrialProductEquiv
    {T : Type*} [Fintype T] (m : ℕ)
    (choice : T → Bool → Bool) :
    {family : T → p3TrialPatternWord m //
      ∀ t : T, family t ∉ p3BadTrialPatternSet m (choice t)} ≃
    ((t : T) →
      {word : p3TrialPatternWord m //
        word ∉ p3BadTrialPatternSet m (choice t)}) where
  toFun family t := ⟨family.1 t, family.2 t⟩
  invFun words := ⟨(fun t => (words t).1), (fun t => (words t).2)⟩
  left_inv family := by cases family; rfl
  right_inv words := by
    funext t
    apply Subtype.ext
    rfl

/-- Exact product formula: among all independent Boolean trial
assignments, the number avoiding every one of the two forbidden
patterns at each trial is (2^(m+1)-2)^|T|. -/
theorem p3GoodTrials_product_card
    {T : Type*} [Fintype T] (m : ℕ) (hm : 0 < m)
    (choice : T → Bool → Bool) :
    Fintype.card
      {family : T → p3TrialPatternWord m //
        ∀ t : T, family t ∉ p3BadTrialPatternSet m (choice t)} =
      (2^(m+1)-2)^(Fintype.card T) := by
  classical
  calc
    Fintype.card
        {family : T → p3TrialPatternWord m //
          ∀ t : T, family t ∉ p3BadTrialPatternSet m (choice t)} =
      Fintype.card ((t : T) →
        {word : p3TrialPatternWord m //
          word ∉ p3BadTrialPatternSet m (choice t)}) :=
        Fintype.card_congr (p3GoodTrialProductEquiv m choice)
    _ = ∏ t : T, Fintype.card
          {word : p3TrialPatternWord m //
            word ∉ p3BadTrialPatternSet m (choice t)} := by
        exact Fintype.card_pi
    _ = ∏ _t : T, (2^(m+1)-2) := by
        apply Finset.prod_congr rfl
        intro t _
        exact p3GoodTrialPatterns_card m hm (choice t)
    _ = (2^(m+1)-2)^(Fintype.card T) := by simp

end Hypertournaments
