import Hypertournaments.EPPA

/-!
# General finite hereditary classes and strong amalgamation

The class predicate is on the original finite presentations. Heredity
includes reindexing by arbitrary orientation-preserving embeddings.
Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:higharity-no-eppa`.
-/

namespace Hypertournaments

abbrev FiniteHyperClass (n : ℕ) := ∀ m : ℕ, Set (Hyper n (Fin m))

def ClassHereditary {n : ℕ} (K : FiniteHyperClass n) : Prop :=
  ∀ {a b : ℕ} (A : Hyper n (Fin a)) (B : Hyper n (Fin b))
    (e : Fin a ↪ Fin b), Preserves A B e → B ∈ K b → A ∈ K a

def ClassHasStrongAmalgamation {n : ℕ} (K : FiniteHyperClass n) : Prop :=
  ∀ (a b c : ℕ) (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c)),
    A ∈ K a → B ∈ K b → C ∈ K c →
    ∀ (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c), Preserves A B f → Preserves A C g →
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
      D ∈ K d ∧ Preserves B D i ∧ Preserves C D j ∧
      (∀ x, i (f x) = j (g x)) ∧
      (∀ y z, i y = j z → ∃ x, f x = y ∧ g x = z)

def ClassUnbounded {n : ℕ} (K : FiniteHyperClass n) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ A : Hyper n (Fin m), A ∈ K m

def ClassHasEPPA {n : ℕ} (K : FiniteHyperClass n) : Prop :=
  ∀ (a : ℕ) (A : Hyper n (Fin a)), A ∈ K a →
    ∃ (b : ℕ) (B : Hyper n (Fin b)) (e : Fin a ↪ Fin b),
      B ∈ K b ∧ A.IsEPPAWitness B e

def omissionClass {n : ℕ} (family : ForbiddenFamily n) : FiniteHyperClass n :=
  fun _ => {A | Omits family A}

theorem omissionClass_hereditary {n : ℕ} (family : ForbiddenFamily n) :
    ClassHereditary (omissionClass family) := by
  intro a b A B e he hB m F hF f hf
  apply hB m F hF (f.trans e)
  intro t
  exact (he (t.trans f)).trans (hf t)

theorem omissionClass_hasStrongAmalgamation_iff {n : ℕ} (family : ForbiddenFamily n) :
    ClassHasStrongAmalgamation (omissionClass family) ↔ HasStrongAmalgamation family :=
  Iff.rfl

theorem omissionClass_hasEPPA_iff {n : ℕ} (family : ForbiddenFamily n) :
    ClassHasEPPA (omissionClass family) ↔ HasEPPA family := Iff.rfl

theorem not_classHasEPPA_of_unrestricted_obstruction {n a : ℕ}
    (K : FiniteHyperClass n) (A : Hyper n (Fin a)) (hA : A ∈ K a)
    (hbad : ¬ A.HasFiniteEPPAWitness) : ¬ ClassHasEPPA K := by
  intro h
  obtain ⟨b, B, e, _, hw⟩ := h a A hA
  exact hbad ⟨b, B, e, hw⟩

end Hypertournaments
