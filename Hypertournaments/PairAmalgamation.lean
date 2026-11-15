import Hypertournaments.PairCompletion
import Hypertournaments.PartialAmalgam
import Hypertournaments.OrderedStrongSpan

/-!
# Strong amalgamation for pair-cancelling omission classes

Source: `tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `prop:link-SAP`.
The carrier contains just the two given sides with exactly their common base
identified. The resulting orientations preserve arbitrary source injections.
-/

namespace Hypertournaments

set_option maxHeartbeats 400000
set_option maxRecDepth 8192

/-- A strong amalgam on the explicit exact-overlap carrier, for arbitrary
finite vertex types and without a nonempty-base assumption. -/
theorem pair_cancelling_strong_span {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Omits family BB) (hC : Omits family CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Omits family D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let : LinearOrder (FiniteStrongSpan.Carrier f g) := LinearOrder.lift' e e.injective
  obtain ⟨P, M, hdist, hdom, hP, hleft, hright⟩ :=
    PartialAmalgam.exists_partial_span family hpc AA BB CC f g hAB hAC hB hC
  obtain ⟨D, hPD, hD⟩ := exists_pair_cancelling_completion (by omega) P M hdist hdom family hpc hP
  exact ⟨D, hD, fun t => hPD _ _ (hleft t), fun t => hPD _ _ (hright t)⟩

/-- The finite-presentation SAP interface, with arbitrary embeddings and exact overlap. -/
theorem pair_cancelling_hasStrongAmalgamation {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    HasStrongAmalgamation family := by
  classical
  intro a b c A B C _hA hB hC f g hf hg
  obtain ⟨D, hD, hi, hj⟩ := pair_cancelling_strong_span hn family hpc A B C f g hf hg hB hC
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let D' := D.pullback e.symm.toEmbedding
  let i := (FiniteStrongSpan.left f g).trans e.toEmbedding
  let j := (FiniteStrongSpan.right f g).trans e.toEmbedding
  refine ⟨Fintype.card (FiniteStrongSpan.Carrier f g), D', i, j,
    omits_pullback hD e.symm.toEmbedding, ?_, ?_, ?_, ?_⟩
  · intro t
    have ht : (t.trans i).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.left f g) := by
      ext k
      simp [i]
    change D.orient ((t.trans i).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hi t
  · intro t
    have ht : (t.trans j).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.right f g) := by
      ext k
      simp [j]
    change D.orient ((t.trans j).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hj t
  · intro x
    exact congrArg e (FiniteStrongSpan.commutes f g x)
  · intro y z heq
    apply (FiniteStrongSpan.overlap f g y z).mp
    exact e.injective heq

/-- The free ordered class has strong amalgamation as well: both given orders
are preserved on the same exact-overlap carrier. -/
theorem pair_cancelling_ordered_strong_span {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {A B C : Type*} [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : Preserves AA BB f.toEmbedding) (hAC : Preserves AA CC g.toEmbedding)
    (hB : Omits family BB) (hC : Omits family CC) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Hyper n (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      Omits family D ∧ Preserves BB D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves CC D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
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
  obtain ⟨order, hiOrder, hjOrder⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  obtain ⟨D, hD, hi, hj⟩ := pair_cancelling_strong_span hn family hpc AA BB CC
    f.toEmbedding g.toEmbedding hAB hAC hB hC
  exact ⟨order, D, hD, hi, hj, hiOrder, hjOrder⟩

end Hypertournaments
