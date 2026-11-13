import Hypertournaments.AllOrderHost
import Hypertournaments.PairOrderHomogeneity
import Hypertournaments.PairRamsey

/-!
# Ordering property for pair-cancelling omission classes

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:ordering`. The witness is fixed before both orders are quantified.
Pair homogeneity forces a copy to be increasing or decreasing in the new
target order; the all-orders host handles either possibility.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Replacing auxiliary orders retains precisely the same intrinsic map. -/
def reorderEmbedding {n : ℕ} {V : Type v} {W : Type w}
    (A : Hyper n V) (B : Hyper n W)
    (oldA newA : LinearOrder V) (oldB newB : LinearOrder W)
    (e : Embedding (toOrderedNative A oldA) (toOrderedNative B oldB))
    (he : @StrictMono V W newA.toPreorder newB.toPreorder e) :
    Embedding (toOrderedNative A newA) (toOrderedNative B newB) :=
  @orderedEmbedding n V W newA newB A B
    (@OrderEmbedding.ofStrictMono V W newA newB.toPreorder e he)
    (preserves_of_orderedEmbedding A B oldA oldB e)

/-- The full ordering property, on arbitrary finite carriers in `Type`.
The target structure is independent of both subsequently chosen orders. -/
theorem pair_cancelling_ordering_property {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {V : Type} [Finite V] (A : Hyper n V) (hA : Omits family A) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper n W), Omits family B ∧
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) := by
  classical
  let P := pairModel n
  let orderP : LinearOrder (Fin 2) := inferInstance
  have hP : Omits family P := pairModel_omits family hpc
  obtain ⟨U, hU, D, oldD, hD, hAll, ⟨baseline⟩⟩ :=
    exists_all_order_host_with hn family hpc A hA P orderP hP
  let : Finite U := hU
  obtain ⟨W, hW, B, oldB, hB, arrow⟩ :=
    exists_ordered_ramsey_witness hn family hpc P D orderP oldD hP hD Bool
  refine ⟨W, hW, B, hB, ?_⟩
  intro orderA orderB
  obtain ⟨f, hf⟩ := arrow (pairOrderColor orderB)
  rcases pair_order_homogeneity hn D oldD B oldB orderB baseline f hf with hmono | hanti
  · obtain ⟨e⟩ := hAll orderA
    have he : @StrictMono V U orderA.toPreorder oldD.toPreorder e := e.strictMono
    exact ⟨reorderEmbedding A B orderA orderA oldB orderB (f.comp e)
      (hmono.comp he)⟩
  · let reversed : LinearOrder V := @OrderDual.instLinearOrder V orderA
    obtain ⟨e⟩ := hAll reversed
    have he : @StrictMono V U reversed.toPreorder oldD.toPreorder e := e.strictMono
    have hcomp : @StrictMono V W orderA.toPreorder orderB.toPreorder (f.comp e) := by
      intro x y hxy
      exact hanti (he hxy)
    exact ⟨reorderEmbedding A B reversed orderA oldB orderB (f.comp e) hcomp⟩

end Hypertournaments.Ramsey
