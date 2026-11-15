import Hypertournaments.FiniteHyperClass
import Hypertournaments.PairCancellation
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Selecting forbidden members of an embedding antichain

The continuum construction in `cor:sullivan-ramsey` associates a different
omission class to every subfamily of a countable pair-cancelling antichain.
This module isolates that elementary part of the argument from the concrete
construction of the antichain and from the construction of homogeneous limits.

Source: `tex_hypertournaments`, commit
`3089ca76522407c9c2a5754df681bfd7d8c0b944`,
`on_homogeneous_hypertournaments.tex`, `cor:sullivan-ramsey`.
-/

namespace Hypertournaments

/-- A finite hypertournament together with its finite cardinality. -/
abbrev FiniteHyper (n : ℕ) := Σ m : ℕ, Hyper n (Fin m)

/-- An ordinary orientation-preserving embedding of finite presentations. -/
def FiniteEmbeds {n : ℕ} (A B : FiniteHyper n) : Prop :=
  ∃ e : Fin A.1 ↪ Fin B.1, Preserves A.2 B.2 e

theorem FiniteEmbeds.refl {n : ℕ} (A : FiniteHyper n) : FiniteEmbeds A A := by
  refine ⟨Function.Embedding.refl _, ?_⟩
  intro t
  rfl

theorem FiniteEmbeds.trans {n : ℕ} {A B C : FiniteHyper n}
    (hAB : FiniteEmbeds A B) (hBC : FiniteEmbeds B C) : FiniteEmbeds A C := by
  obtain ⟨e, he⟩ := hAB
  obtain ⟨f, hf⟩ := hBC
  refine ⟨e.trans f, ?_⟩
  intro t
  exact (hf (t.trans e)).trans (he t)

/-- A sequence of pair-cancelling finite structures forming an antichain under
ordinary embeddings. The implication includes the reflexive case. -/
structure IndexedPCAntichain (n : ℕ) where
  member : ℕ → FiniteHyper n
  pairCancelling : ∀ i, PairCancelling (member i).2
  incomparable : ∀ i j, FiniteEmbeds (member i) (member j) → i = j

/-- Select exactly the displayed presentations with indices in `S`.
Omission itself already quantifies over all copies via arbitrary embeddings. -/
def selectedForbiddenFamily {n : ℕ} (A : IndexedPCAntichain n) (S : Set ℕ) :
    ForbiddenFamily n :=
  fun m F => ∃ i, i ∈ S ∧ A.member i = ⟨m, F⟩

theorem selectedForbiddenFamily_pairCancelling {n : ℕ}
    (A : IndexedPCAntichain n) (S : Set ℕ) :
    ∀ m F, F ∈ selectedForbiddenFamily A S m → PairCancelling F := by
  intro m F hF
  obtain ⟨i, _, hi⟩ := hF
  exact (congrArg (fun B : FiniteHyper n => PairCancelling B.2) hi).mp
    (A.pairCancelling i)

/-- Omission of the selected family is precisely non-embedding of every
selected member. This also handles structures outside the antichain. -/
theorem omits_selectedForbiddenFamily_iff {n : ℕ}
    (A : IndexedPCAntichain n) (S : Set ℕ) (B : FiniteHyper n) :
    Omits (selectedForbiddenFamily A S) B.2 ↔
      ∀ i, i ∈ S → ¬ FiniteEmbeds (A.member i) B := by
  constructor
  · intro h i hi hEmb
    obtain ⟨e, he⟩ := hEmb
    exact h (A.member i).1 (A.member i).2 ⟨i, hi, rfl⟩ e he
  · intro h m F hF e he
    obtain ⟨i, hi, hEq⟩ := hF
    have hEmb : FiniteEmbeds (⟨m, F⟩ : FiniteHyper n) B := ⟨e, he⟩
    exact h i hi (hEq.symm ▸ hEmb)

/-- The displayed member is omitted exactly when its own index was not selected. -/
theorem omits_member_iff {n : ℕ}
    (A : IndexedPCAntichain n) (S : Set ℕ) (i : ℕ) :
    Omits (selectedForbiddenFamily A S) (A.member i).2 ↔ i ∉ S := by
  rw [omits_selectedForbiddenFamily_iff]
  constructor
  · intro h hi
    exact h i hi (FiniteEmbeds.refl _)
  · intro hi j hj hEmb
    exact hi (A.incomparable j i hEmb ▸ hj)

/-- Distinct selections have distinct ages already on finite presentations. -/
theorem omissionClass_selectedForbiddenFamily_injective {n : ℕ}
    (A : IndexedPCAntichain n) :
    Function.Injective (fun S : Set ℕ => omissionClass (selectedForbiddenFamily A S)) := by
  intro S T hST
  change omissionClass (selectedForbiddenFamily A S) =
    omissionClass (selectedForbiddenFamily A T) at hST
  apply Set.ext
  intro i
  have hOmit :
      Omits (selectedForbiddenFamily A S) (A.member i).2 ↔
        Omits (selectedForbiddenFamily A T) (A.member i).2 := by
    change (A.member i).2 ∈ omissionClass (selectedForbiddenFamily A S) (A.member i).1 ↔
      (A.member i).2 ∈ omissionClass (selectedForbiddenFamily A T) (A.member i).1
    rw [hST]
  have hNot : i ∉ S ↔ i ∉ T :=
    (omits_member_iff A S i).symm.trans (hOmit.trans (omits_member_iff A T i))
  exact not_iff_not.mp hNot

/-- The separation is witnessed by one of the original antichain members. -/
theorem selected_omissionClasses_distinct {n : ℕ}
    (A : IndexedPCAntichain n) {S T : Set ℕ} (hST : S ≠ T) :
    omissionClass (selectedForbiddenFamily A S) ≠
      omissionClass (selectedForbiddenFamily A T) := by
  exact fun h => hST (omissionClass_selectedForbiddenFamily_injective A h)

/-- A finite forbidden basis, expressed using arbitrary finite presentations
rather than requiring a common vertex set or an isomorphism quotient. -/
def ClassFinitelyBounded {n : ℕ} (K : FiniteHyperClass n) : Prop :=
  ∃ (k : ℕ) (basis : Fin k → FiniteHyper n),
    ∀ (m : ℕ) (B : Hyper n (Fin m)),
      B ∈ K m ↔ ∀ j, ¬ FiniteEmbeds (basis j) ⟨m, B⟩

/-- Any finite forbidden basis can exclude only finitely many members of an
embedding antichain. No assumptions on the sizes of the proposed basis are used. -/
theorem finite_of_selected_omissionClass_finitelyBounded {n : ℕ}
    (A : IndexedPCAntichain n) (S : Set ℕ)
    (h : ClassFinitelyBounded (omissionClass (selectedForbiddenFamily A S))) :
    S.Finite := by
  classical
  obtain ⟨k, basis, hBasis⟩ := h
  have hWitness : ∀ j : Fin k, ∃ i, i ∈ S ∧ FiniteEmbeds (A.member i) (basis j) := by
    intro j
    have hNot : ¬ Omits (selectedForbiddenFamily A S) (basis j).2 := by
      intro hOmit
      have hAvoid := (hBasis (basis j).1 (basis j).2).mp hOmit
      exact hAvoid j (FiniteEmbeds.refl _)
    rw [omits_selectedForbiddenFamily_iff] at hNot
    by_contra hNone
    exact hNot (fun i hi hEmb => hNone ⟨i, hi, hEmb⟩)
  let index : Fin k → ℕ := fun j => Classical.choose (hWitness j)
  have hIndex (j : Fin k) :
      index j ∈ S ∧ FiniteEmbeds (A.member (index j)) (basis j) :=
    Classical.choose_spec (hWitness j)
  apply (Set.finite_range index).subset
  intro i hi
  have hNot : ¬ Omits (selectedForbiddenFamily A S) (A.member i).2 := by
    exact fun hOmit => (omits_member_iff A S i).mp hOmit hi
  have hNotBasis : ¬ ∀ j, ¬ FiniteEmbeds (basis j) (A.member i) := by
    intro hAvoid
    exact hNot ((hBasis (A.member i).1 (A.member i).2).mpr hAvoid)
  have hEmb : ∃ j, FiniteEmbeds (basis j) (A.member i) := by
    simpa only [not_forall, not_not] using hNotBasis
  obtain ⟨j, hj⟩ := hEmb
  exact ⟨j, A.incomparable (index j) i ((hIndex j).2.trans hj)⟩

theorem selected_omissionClass_not_finitelyBounded {n : ℕ}
    (A : IndexedPCAntichain n) {S : Set ℕ} (hS : S.Infinite) :
    ¬ ClassFinitelyBounded (omissionClass (selectedForbiddenFamily A S)) := by
  exact fun h => hS (finite_of_selected_omissionClass_finitelyBounded A S h)

/-- Encode an arbitrary subset in the even indices and include every odd index.
Thus the selected family stays infinite without losing any subset information. -/
def infiniteSelection (S : Set ℕ) : Set ℕ :=
  {i | ∃ k, i = 2 * k + 1 ∨ (i = 2 * k ∧ k ∈ S)}

theorem even_mem_infiniteSelection (S : Set ℕ) (i : ℕ) :
    2 * i ∈ infiniteSelection S ↔ i ∈ S := by
  constructor
  · rintro ⟨k, hk | ⟨hk, hmem⟩⟩
    · omega
    · have hki : k = i := by omega
      exact hki ▸ hmem
  · exact fun hi => ⟨i, Or.inr ⟨rfl, hi⟩⟩

theorem infiniteSelection_infinite (S : Set ℕ) : (infiniteSelection S).Infinite := by
  have hInjective : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega
  apply (Set.infinite_range_of_injective hInjective).mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i, Or.inl rfl⟩

theorem infiniteSelection_injective : Function.Injective infiniteSelection := by
  intro S T hST
  apply Set.ext
  intro i
  have hEven : 2 * i ∈ infiniteSelection S ↔ 2 * i ∈ infiniteSelection T := by
    rw [hST]
  simpa only [even_mem_infiniteSelection] using hEven

/-- A powerset-indexed family of distinct classes, each of which requires an
infinite forbidden basis. This is the finite-age part of the continuum corollary. -/
theorem continuum_not_finitelyBounded_classes {n : ℕ} (A : IndexedPCAntichain n) :
    ∃ K : Set ℕ → FiniteHyperClass n,
      Function.Injective K ∧ ∀ S, ¬ ClassFinitelyBounded (K S) := by
  refine ⟨fun S => omissionClass (selectedForbiddenFamily A (infiniteSelection S)), ?_, ?_⟩
  · exact (omissionClass_selectedForbiddenFamily_injective A).comp
      infiniteSelection_injective
  · intro S
    exact selected_omissionClass_not_finitelyBounded A (infiniteSelection_infinite S)

/-- The displayed collection of distinct ages has cardinality exactly continuum. -/
theorem selected_infinite_classes_cardinality {n : ℕ} (A : IndexedPCAntichain n) :
    Cardinal.mk (Set.range (fun S : Set ℕ =>
      omissionClass (selectedForbiddenFamily A (infiniteSelection S)))) =
        Cardinal.continuum := by
  exact (Cardinal.mk_range_eq _
    ((omissionClass_selectedForbiddenFamily_injective A).comp
      infiniteSelection_injective)).trans Cardinal.mk_set_nat

end Hypertournaments
