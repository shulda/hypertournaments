import Hypertournaments.Amalgamation

/-!
# Ordinary amalgamation obstructions

Generic bridge between an explicitly non-amalgamable finite span
and failure of the amalgamation property. No strong amalgamation
condition is imposed.
-/

namespace Hypertournaments

/-- An ordinary amalgam of the displayed span, with possible
identifications between the two larger vertex sets. -/
def HasAmalgam {n a b c : ℕ} (S : Set ℕ)
    (_A : Hyper n (Fin a)) (B : Hyper n (Fin b))
    (C : Hyper n (Fin c))
    (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c) : Prop :=
  ∃ (d : ℕ) (D : Hyper n (Fin d))
    (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
    Admissible S D ∧ Preserves B D i ∧ Preserves C D j ∧
      (∀ x : Fin a, i (f x) = j (g x))

/-- Any single span admitting no ordinary amalgam disproves AP. -/
theorem not_hasAP_of_no_amalgam
    {n a b c : ℕ} {S : Set ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin b))
    (C : Hyper n (Fin c))
    (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c)
    (hA : Admissible S A) (hB : Admissible S B)
    (hC : Admissible S C)
    (hAB : Preserves A B f) (hAC : Preserves A C g)
    (hno : ¬ HasAmalgam S A B C f g) :
    ¬ HasAP n S := by
  intro hAP
  apply hno
  exact hAP a b c A B C hA hB hC f g hAB hAC

/-- Canonical embedding of an a-element base into its
one-point extension. -/
def onePointBaseEmbedding (a : ℕ) : Fin a ↪ Fin (a + 1) :=
  Fin.castSuccEmb

/-- An ordinary amalgam of two extensions over the
canonical common a-element base. -/
def OnePointHasAmalgam {n a : ℕ} (S : Set ℕ)
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1))) : Prop :=
  HasAmalgam S A L R (onePointBaseEmbedding a)
    (onePointBaseEmbedding a)

/-- A bad one-point span is enough to disprove ordinary AP. -/
theorem not_hasAP_of_no_onePoint_amalgam
    {n a : ℕ} {S : Set ℕ}
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1)))
    (hA : Admissible S A) (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hno : ¬ OnePointHasAmalgam S A L R) :
    ¬ HasAP n S := by
  exact not_hasAP_of_no_amalgam A L R
    (onePointBaseEmbedding a) (onePointBaseEmbedding a)
    hA hL hR hAL hAR hno

end Hypertournaments
