import Hypertournaments.Affine.ExpansionCoding
import Hypertournaments.Affine.PairOrdering

/-!
# The ordering property for actual potential expansions

Source: `tex_hypertournaments` at
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`generalised_potential_structures_proof.tex`, `lem:ordering`.
The target potential and raw labels are fixed before either free order is
chosen. A single source code is decoded independently of these later orders.
-/

namespace Hypertournaments.Affine

universe u v w

open StructuralRamsey
open StructuralRamsey.Structure

theorem expansion_ordering_property {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u} {G : Type v} [AddCommGroup G] (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {V : Type w} [Finite V] (A : Expansion r d V) :
    ∃ (W : Type w) (_ : Finite W) (B : Expansion r d W),
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedExpansion A orderA) (toOrderedExpansion B orderB)) := by
  classical
  let : Nonempty Q := ⟨Classical.choose (d.onto 0)⟩
  let : Fintype V := Fintype.ofFinite V
  let canonical : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let P := A.toCodePair canonical
  obtain ⟨W, hW, target, hOrder⟩ :=
    pair_ordering_property hr (Palette.affine d.offset) (Palette.free Q) P
  refine ⟨W, hW, d.decodePair ha target, ?_⟩
  intro orderA orderB
  obtain ⟨e⟩ := hOrder orderA orderB
  have he := preserves_of_pairOrderedEmbedding P target orderA orderB e
  have hDecode := d.decodePair_preserves ha P target e.toFunctionEmbedding he
  dsimp only [P] at hDecode
  rw [A.decode_toCodePair ha canonical] at hDecode
  let := orderA
  let := orderB
  let eo : V ↪o W := OrderEmbedding.ofStrictMono e e.strictMono
  exact ⟨expansionOrderedEmbedding A (d.decodePair ha target) eo hDecode⟩

end Hypertournaments.Affine
