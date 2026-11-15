import Hypertournaments.BinaryAmalgamation
import Hypertournaments.CyclicAmalgamation
import Hypertournaments.SmallArityPalettes
import Hypertournaments.LocalAmalgamationTransport
import Hypertournaments.UnboundedClassification
import Hypertournaments.UnrestrictedAmalgamation
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# Strong amalgamation in every unbounded locally constrained AP class

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:constrained-classification`. The two binary and four ternary palettes
all have strong amalgamation. In higher arity the proved negative
classification reduces ordinary AP to the two positive constructions.
Impossible palette indices are removed only internally.
-/

namespace Hypertournaments

theorem switchingAllowed_three : switchingAllowed 3 = ({0, 2} : Set ℕ) := by
  ext d
  simp only [switchingAllowed, centralIndex, Set.mem_ofPred_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Both valid unbounded binary palettes have actual strong amalgams. -/
theorem binary_central_strong_span (S : Set ℕ) (hvalid : ValidTypes 2 S)
    (hcentral : centralIndex 2 ∈ S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper 2 A) (BB : Hyper 2 B) (CC : Hyper 2 C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper 2 (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  rcases binary_central_palette_cases S hvalid hcentral with rfl | rfl
  · exact binary_transitive_strong_span AA BB CC f g hAB hAC hB hC
  · obtain ⟨D, hi, hj⟩ := unrestricted_strong_span (by decide) AA BB CC f g hAB hAC
    refine ⟨D, ?_, hi, hj⟩
    intro t
    have hb := localIndex_le_central D t
    change localIndex D t ≤ 1 at hb
    have hcases : localIndex D t = 0 ∨ localIndex D t = 1 := by omega
    rcases hcases with h | h <;> simp [h]

/-- All four valid unbounded ternary palettes have actual strong amalgams. -/
theorem ternary_central_strong_span (S : Set ℕ) (hvalid : ValidTypes 3 S)
    (hcentral : centralIndex 3 ∈ S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper 3 A) (BB : Hyper 3 B) (CC : Hyper 3 C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper 3 (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  rcases ternary_central_palette_cases S hvalid hcentral with rfl | rfl | rfl | rfl
  · exact cyclic_strong_span AA BB CC f g hAB hAC hB hC
  · rw [← switchingAllowed_three] at hB hC ⊢
    exact switching_strong_span (by decide) (by decide) AA BB CC f g hAB hAC hB hC
  · exact central_next_strong_span (by decide) {1, 2}
      (by decide) (by decide) AA BB CC f g hAB hAC hB hC
  · exact central_next_strong_span (by decide) {0, 1, 2}
      (by decide) (by decide) AA BB CC f g hAB hAC hB hC

/-- Central membership alone gives strong amalgamation in arities two and
three, without a validity assumption on the original allowed set. -/
theorem small_arity_central_strong_span {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  let T := S ∩ Set.Iic (centralIndex n)
  have hvalid : ValidTypes n T := fun _ hd => hd.2
  have hcentralT : centralIndex n ∈ T := ⟨hcentral, by simp⟩
  have hBT : Admissible T BB := (admissible_validize S BB).mp hB
  have hCT : Admissible T CC := (admissible_validize S CC).mp hC
  have hn : n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl
  · obtain ⟨D, hD, hi, hj⟩ := binary_central_strong_span T hvalid hcentralT
      AA BB CC f g hAB hAC hBT hCT
    exact ⟨D, (admissible_validize S D).mpr hD, hi, hj⟩
  · obtain ⟨D, hD, hi, hj⟩ := ternary_central_strong_span T hvalid hcentralT
      AA BB CC f g hAB hAC hBT hCT
    exact ⟨D, (admissible_validize S D).mpr hD, hi, hj⟩

/-- Every unbounded small-arity palette has strong amalgamation; ordinary
AP need not be assumed in this case. -/
theorem small_arity_unbounded_hasStrongAmalgamation {n : ℕ}
    (hn2 : 2 ≤ n) (hn3 : n ≤ 3) (S : Set ℕ) (hU : UnboundedAdmissible n S) :
    HasStrongAmalgamation (localForbiddenFamily n S) := by
  apply local_hasStrongAmalgamation_of_strong_span S
  intro a b c A B C f g hf hg hB hC
  exact small_arity_central_strong_span hn2 hn3 S
    ((unboundedAdmissible_iff_central n S).mp hU) A B C f g hf hg hB hC

/-- Ordinary AP supplies actual strong amalgams in every arity at least two
when the central type is allowed. Phantom indices have no effect. -/
theorem strong_span_of_hasAP_all_arities {n : ℕ} (hn : 2 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hAP : HasAP n S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  by_cases hsmall : n ≤ 3
  · exact small_arity_central_strong_span hn hsmall S hcentral
      AA BB CC f g hAB hAC hB hC
  · let T := S ∩ Set.Iic (centralIndex n)
    have hvalid : ValidTypes n T := fun _ hd => hd.2
    have hcentralT : centralIndex n ∈ T := ⟨hcentral, by simp⟩
    have hAPT : HasAP n T := (hasAP_validize n S).mp hAP
    obtain ⟨D, hD, hi, hj⟩ := strong_span_of_hasAP (by omega) T hvalid hcentralT hAPT
      AA BB CC f g hAB hAC ((admissible_validize S BB).mp hB)
      ((admissible_validize S CC).mp hC)
    exact ⟨D, (admissible_validize S D).mpr hD, hi, hj⟩

/-- The article's AP-to-SAP assertion, uniformly in every arity at least two. -/
theorem unbounded_hasAP_iff_hasStrongAmalgamation {n : ℕ} (hn : 2 ≤ n)
    (S : Set ℕ) (hU : UnboundedAdmissible n S) :
    HasAP n S ↔ HasStrongAmalgamation (localForbiddenFamily n S) := by
  constructor
  · intro hAP
    apply local_hasStrongAmalgamation_of_strong_span S
    intro a b c A B C f g hf hg hB hC
    exact strong_span_of_hasAP_all_arities hn S
      ((unboundedAdmissible_iff_central n S).mp hU) hAP A B C f g hf hg hB hC
  · exact local_hasAP_of_hasStrongAmalgamation S

/-- A single ordinary-AP criterion now includes the two small arities. -/
theorem amalgamation_classification_all_arities (n : ℕ) (hn : 2 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) (hcentral : centralIndex n ∈ S) :
    HasAP n S ↔ n ≤ 3 ∨ NecessaryAlternatives n S := by
  by_cases hsmall : n ≤ 3
  · have hSAP := small_arity_unbounded_hasStrongAmalgamation hn hsmall S
      ((unboundedAdmissible_iff_central n S).mpr hcentral)
    exact ⟨fun _ => Or.inl hsmall, fun _ => local_hasAP_of_hasStrongAmalgamation S hSAP⟩
  · constructor
    · intro hAP
      exact Or.inr ((amalgamation_classification n (by omega) S hvalid hcentral).mp hAP)
    · intro h
      exact (amalgamation_classification n (by omega) S hvalid hcentral).mpr
        (h.resolve_left hsmall)

/-- The same criterion with unboundedness as its source-level premise. -/
theorem unbounded_amalgamation_classification_all_arities (n : ℕ) (hn : 2 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) (hU : UnboundedAdmissible n S) :
    HasAP n S ↔ n ≤ 3 ∨ NecessaryAlternatives n S :=
  amalgamation_classification_all_arities n hn S hvalid
    ((unboundedAdmissible_iff_central n S).mp hU)

end Hypertournaments
