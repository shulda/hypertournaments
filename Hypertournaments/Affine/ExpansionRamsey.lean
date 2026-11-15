import Hypertournaments.Affine.ExpansionCoding
import Hypertournaments.Affine.PairRamsey
import Mathlib.Tactic.Ext

/-!
# Actual Ramsey witnesses for affine potential expansions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Independent potential labels and free
oriented fiber codes have actual finite Ramsey witnesses. Equivariant
decoding transports them to expansions naming the original raw labels,
an actual compatible potential, and a free linear order.
-/

universe u v w z

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

variable {Q : Type u} {G : Type v} [AddCommGroup G]

/-- An actual finite Ramsey witness in the original expanded native language.
Finiteness of the palettes is only needed for precompactness, not this arrow. -/
theorem exists_expansion_ordered_ramsey_witness (r : ℕ) (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {V W : Type w} [Finite V] [Finite W]
    (A : Expansion r d V) (B : Expansion r d W)
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (κ : Type z) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type w) (_ : Finite X) (D : Expansion r d X) (order : LinearOrder X),
      Structure.Arrow (toOrderedExpansion A orderA) (toOrderedExpansion B orderB)
        (toOrderedExpansion D order) κ := by
  classical
  let : Nonempty Q := ⟨Classical.choose (d.onto 0)⟩
  obtain ⟨X, hX, C, order, arrow⟩ :=
    exists_pair_ordered_ramsey_witness r (Palette.affine d.offset) (Palette.free Q)
      (A.toCodePair orderA) (B.toCodePair orderB) orderA orderB κ
  let D := d.decodePair ha C
  refine ⟨X, hX, D, order, ?_⟩
  intro χ
  let χ' : Embedding (toOrderedPair (A.toCodePair orderA) orderA)
      (toOrderedPair C order) → κ :=
    fun e => χ (expansionEmbeddingOfCodeEmbedding ha A orderA C order e)
  obtain ⟨f, hf⟩ := arrow χ'
  refine ⟨expansionEmbeddingOfCodeEmbedding ha B orderB C order f, ?_⟩
  intro e₁ e₂
  have hh := hf (codeEmbeddingOfExpansionEmbedding A B orderA orderB e₁)
    (codeEmbeddingOfExpansionEmbedding A B orderA orderB e₂)
  have he (e : Embedding (toOrderedExpansion A orderA) (toOrderedExpansion B orderB)) :
      expansionEmbeddingOfCodeEmbedding ha A orderA C order
          (f.comp (codeEmbeddingOfExpansionEmbedding A B orderA orderB e)) =
        (expansionEmbeddingOfCodeEmbedding ha B orderB C order f).comp e := by
    apply Embedding.ext
    intro x
    rfl
  simpa only [χ', he] using hh

/-- The full native class of actual affine potential expansions, equipped
with free linear orders, is Ramsey. -/
theorem expansion_ordered_ramsey (r : ℕ) (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0) :
    CCO.UnaryHN.Native.Ramsey.{max u v,w,z} (orderedExpansionClass (r := r) d) := by
  intro V W _ _ A B hA hB κ _ _
  rcases hA with ⟨hV, AA, orderA, rfl⟩
  rcases hB with ⟨hW, BB, orderB, rfl⟩
  let : Finite V := hV
  let : Finite W := hW
  obtain ⟨X, hX, D, order, arrow⟩ :=
    exists_expansion_ordered_ramsey_witness r d ha AA BB orderA orderB κ
  exact ⟨X, hX, toOrderedExpansion D order, ⟨hX, D, order, rfl⟩, arrow⟩

end Hypertournaments.Affine
