import Hypertournaments.LocalTypes

/-!
# Ordinary (not strong) amalgamation

For the moment all finite structures have their underlying vertex sets
presented as Fin k. In particular, k is arbitrary, including zero.
No linear-order-preservation condition is imposed on embeddings.
The later bridge to arbitrary finite types is just reindexing.
-/

namespace Hypertournaments

/-- Ordinary amalgamation for the age cut out by allowed local indices.
The two images are permitted to identify vertices outside the base. -/
def HasAP (n : ℕ) (S : Set ℕ) : Prop :=
  ∀ (a b c : ℕ)
    (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c)),
      Admissible S A → Admissible S B → Admissible S C →
      ∀ (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c),
      Preserves A B f → Preserves A C g →
      ∃ (d : ℕ) (D : Hyper n (Fin d))
        (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
        Admissible S D ∧ Preserves B D i ∧ Preserves C D j ∧
          (∀ x : Fin a, i (f x) = j (g x))

/-- Removing impossible local-type indices does not affect ordinary AP.
This makes the classification's well-formed allowed-type interface exact:
phantom indices above q have no mathematical effect on the age. -/
theorem hasAP_validize (n : ℕ) (S : Set ℕ) :
    HasAP n S ↔ HasAP n (S ∩ Set.Iic (centralIndex n)) := by
  constructor
  · intro hAP a b c A B C hA hB hC f g hAB hAC
    obtain ⟨d, D, i, j, hD, hi, hj, hcomm⟩ :=
      hAP a b c A B C
        ((admissible_validize S A).2 hA)
        ((admissible_validize S B).2 hB)
        ((admissible_validize S C).2 hC)
        f g hAB hAC
    exact ⟨d, D, i, j, (admissible_validize S D).1 hD, hi, hj, hcomm⟩
  · intro hAP a b c A B C hA hB hC f g hAB hAC
    obtain ⟨d, D, i, j, hD, hi, hj, hcomm⟩ :=
      hAP a b c A B C
        ((admissible_validize S A).1 hA)
        ((admissible_validize S B).1 hB)
        ((admissible_validize S C).1 hC)
        f g hAB hAC
    exact ⟨d, D, i, j, (admissible_validize S D).2 hD, hi, hj, hcomm⟩

/-!
Intended theorem to prove after source audit:

theorem negative_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hap : HasAP n S) : NecessaryAlternatives n S := ...

The positive construction can later prove the converse directly against
the same HasAP definition. No proof placeholder or axiom is introduced.
-/

end Hypertournaments
