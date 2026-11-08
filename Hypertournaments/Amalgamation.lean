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

/-!
Intended theorem to prove after source audit:

theorem negative_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S)
    (hap : HasAP n S) : NecessaryAlternatives n S := ...

The positive construction can later prove the converse directly against
the same HasAP definition. No proof placeholder or axiom is introduced.
-/

end Hypertournaments
