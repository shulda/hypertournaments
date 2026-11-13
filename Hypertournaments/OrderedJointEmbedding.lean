import Lean.Elab.Tactic.Omega
import Hypertournaments.RamseyClass

/-!
# Ordered joint embeddings and finite joint hosts

The positive-arity relational language has one common empty model. Ordered
SAP therefore gives JEP, including for empty sources. Finite families are
joined by an actual finite induction; no host provider is assumed.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- The unique empty positive-arity ordered model, lifted to the carrier universe. -/
def emptyOrderedNative (n : ℕ) : Structure (orderedLanguage n) PEmpty.{v + 1} where
  rel _ _ := False
  func F := nomatch F

/-- No tuple in either positive relation arity can have empty carrier. -/
def emptyOrderedEmbedding {n : ℕ} (hn : 0 < n) {V : Type v}
    (C : Structure (orderedLanguage n) V) : Embedding (emptyOrderedNative n) C where
  toFun := PEmpty.elim
  injective := fun x => isEmptyElim x
  map_rel_iff R t := by
    cases R with
    | inl R => exact isEmptyElim (t ⟨0, hn⟩)
    | inr R => exact isEmptyElim (t ⟨0, by change 0 < 2; decide⟩)
  map_func F := nomatch F

/-- Binary ordered JEP obtained from the proved SAP over the actual common empty model. -/
theorem ordered_jointEmbedding {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {V W : Type v} (A : Structure (orderedLanguage n) V) (B : Structure (orderedLanguage n) W)
    (hA : orderedOmissionClass family A) (hB : orderedOmissionClass family B) :
    ∃ (X : Type v) (_ : Finite X) (D : Structure (orderedLanguage n) X),
      orderedOmissionClass family D ∧ Nonempty (Embedding A D) ∧ Nonempty (Embedding B D) := by
  obtain ⟨X, hX, D, hD, i, j, _, _⟩ :=
    (orderedOmissionClass_finiteHereditarySAP hn family hpc).strong hA hB
      (emptyOrderedEmbedding (by omega) A) (emptyOrderedEmbedding (by omega) B)
  exact ⟨X, hX, D, hD, ⟨i⟩, ⟨j⟩⟩

/-- A finite family has one finite joint host retaining a supplied anchor copy.
The anchor also handles the empty index family. -/
theorem finite_ordered_jointEmbedding {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {I : Type w} (indices : Finset I) (Carrier : I → Type v)
    (models : ∀ i, Structure (orderedLanguage n) (Carrier i))
    (hmodels : ∀ i, orderedOmissionClass family (models i))
    {U : Type v} (anchor : Structure (orderedLanguage n) U)
    (hanchor : orderedOmissionClass family anchor) :
    ∃ (X : Type v) (_ : Finite X) (D : Structure (orderedLanguage n) X),
      orderedOmissionClass family D ∧ Nonempty (Embedding anchor D) ∧
      ∀ i ∈ indices, Nonempty (Embedding (models i) D) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    exact ⟨U, hanchor.1, anchor, hanchor, ⟨Embedding.id _⟩, by simp⟩
  | @insert i indices hi ih =>
    obtain ⟨X, hX, D, hD, ⟨eAnchor⟩, hEach⟩ := ih
    obtain ⟨Y, hY, E, hE, ⟨eD⟩, ⟨eI⟩⟩ :=
      ordered_jointEmbedding hn family hpc D (models i) hD (hmodels i)
    refine ⟨Y, hY, E, hE, ⟨eD.comp eAnchor⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨eI⟩
    · obtain ⟨ej⟩ := hEach j hj
      exact ⟨eD.comp ej⟩

/-- Finitely many indexed models have a common ordered host, with an anchor. -/
theorem all_finite_ordered_jointEmbedding {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {I : Type w} [Finite I] (Carrier : I → Type v)
    (models : ∀ i, Structure (orderedLanguage n) (Carrier i))
    (hmodels : ∀ i, orderedOmissionClass family (models i))
    {U : Type v} (anchor : Structure (orderedLanguage n) U)
    (hanchor : orderedOmissionClass family anchor) :
    ∃ (X : Type v) (_ : Finite X) (D : Structure (orderedLanguage n) X),
      orderedOmissionClass family D ∧ Nonempty (Embedding anchor D) ∧
      ∀ i, Nonempty (Embedding (models i) D) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨X, hX, D, hD, hAnchor, hEach⟩ :=
    finite_ordered_jointEmbedding hn family hpc Finset.univ Carrier models hmodels anchor hanchor
  exact ⟨X, hX, D, hD, hAnchor, fun i => hEach i (Finset.mem_univ i)⟩

end Hypertournaments.Ramsey
