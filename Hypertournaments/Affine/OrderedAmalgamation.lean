import Hypertournaments.Affine.Amalgamation
import Hypertournaments.OrderedStrongSpan

/-!
# Strong amalgamation retaining the free orders

Source: `tex_hypertournaments` at
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`generalised_potential_structures_proof.tex`, `prop:sap`.
The actual raw and potential embeddings retain exactly the prescribed
overlap, and the same carrier admits an order extending both side orders.
-/

namespace Hypertournaments.Affine

universe u v w z s

theorem expanded_ordered_strong_span {r : ℕ}
    {Q : Type u} {G : Type v} [AddCommGroup G] (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {A : Type w} {B : Type z} {C : Type s}
    [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Expansion r d A) (BB : Expansion r d B) (CC : Expansion r d C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : AA.Preserves BB f.toEmbedding) (hAC : AA.Preserves CC g.toEmbedding) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Expansion r d (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      BB.Preserves D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      CC.Preserves D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨order, hi, hj⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  obtain ⟨D, hB, hC⟩ := expanded_strong_span d ha AA BB CC
    f.toEmbedding g.toEmbedding hAB hAC
  exact ⟨order, D, hB, hC, hi, hj⟩

end Hypertournaments.Affine
