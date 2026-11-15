import Hypertournaments.Affine.PairOrderHost
import Hypertournaments.Affine.PairRamsey
import Hypertournaments.Affine.PairOrderWitness

/-!
# The ordering property for free pairs of labelled structures

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the expansion property in `Further potential constructions`.
One Ramsey-homogeneous edge type suffices after inserting a point between
each original pair. The target is fixed before either free order is chosen.
-/

namespace Hypertournaments.Affine

universe u₁ u₂ v w

open StructuralRamsey
open StructuralRamsey.Structure

noncomputable section

/-- Retain the same intrinsic embedding while changing its auxiliary orders. -/
def pairReorderEmbedding {r : ℕ} {Q : Type u₁} {K : Type u₂}
    {P : Palette Q} {R : Palette K} {V : Type v} {W : Type w}
    (A : Pair r P R V) (B : Pair r P R W)
    (oldA newA : LinearOrder V) (oldB newB : LinearOrder W)
    (e : Embedding (toOrderedPair A oldA) (toOrderedPair B oldB))
    (he : @StrictMono V W newA.toPreorder newB.toPreorder e) :
    Embedding (toOrderedPair A newA) (toOrderedPair B newB) :=
  @pairOrderedEmbedding r Q K P R V W newA newB A B
    (@OrderEmbedding.ofStrictMono V W newA newB.toPreorder e he)
    (preserves_of_pairOrderedEmbedding A B oldA oldB e)

private def liftedPairEdge {r : ℕ} {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) (q : Q) (k : K) : Pair r P R (ULift.{v} (Fin 2)) :=
  (pairEdgeModel r P R q k).pullback ⟨ULift.down, ULift.down_injective⟩

private def liftedPairEdgeDown {r : ℕ} {Q : Type u₁} {K : Type u₂}
    (P : Palette Q) (R : Palette K) (q : Q) (k : K) :
    Embedding (toOrderedPair (liftedPairEdge.{u₁,u₂,v} P R q k) inferInstance)
      (orderedPairEdgeModel r P R q k) := by
  let e : ULift.{v} (Fin 2) ↪o Fin 2 := OrderEmbedding.ofStrictMono ULift.down
    (fun _ _ h => h)
  exact pairOrderedEmbedding _ _ e ((pairEdgeModel r P R q k).preserves_pullback e.toEmbedding)

/-- The full ordering property on arbitrary finite carriers, including the
binary lower arity and palettes with involution-fixed labels. -/
theorem pair_ordering_property {r : ℕ} (hr : 2 ≤ r)
    {Q : Type u₁} {K : Type u₂} [Nonempty Q] [Nonempty K]
    (P : Palette Q) (R : Palette K) {V : Type v} [Finite V] (A : Pair r P R V) :
    ∃ (W : Type v) (_ : Finite W) (B : Pair r P R W),
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedPair A orderA) (toOrderedPair B orderB)) := by
  classical
  let q : Q := Classical.choice inferInstance
  let k : K := Classical.choice inferInstance
  let : Fintype V := Fintype.ofFinite V
  let enum := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' enum enum.injective
  obtain ⟨U, hU, D, orderD, hAll, _anchor⟩ :=
    exists_all_pair_order_host_with hr P R A A canonical
  let : Finite U := hU
  let : LinearOrder U := orderD
  let E := pairOrderWitness D q k
  let j := pairOrderWitness_oldEmbedding D q k
  let edge : Pair r P R (ULift.{v} (Fin 2)) := liftedPairEdge P R q k
  obtain ⟨W, hW, B, oldB, arrow⟩ := exists_pair_ordered_ramsey_witness r P R edge E
    inferInstance (orderWitnessOrder U) Bool
  refine ⟨W, hW, B, ?_⟩
  intro orderA orderB
  let colour : Embedding (toOrderedPair edge inferInstance) (toOrderedPair B oldB) → Bool :=
    fun e => decide (@LT.lt W orderB.toLT (e ⟨0⟩) (e ⟨1⟩))
  obtain ⟨f, hf⟩ := arrow colour
  have hhom : ∀ e₁ e₂ : Embedding (orderedPairEdgeModel r P R q k)
      (toOrderedPair E (orderWitnessOrder U)),
      pairEdgeOrderColor orderB (f.comp e₁) = pairEdgeOrderColor orderB (f.comp e₂) := by
    intro e₁ e₂
    exact hf (e₁.comp (liftedPairEdgeDown P R q k)) (e₂.comp (liftedPairEdgeDown P R q k))
  rcases pairOrderWitness_homogeneity hr D q k B oldB orderB f hhom with hmono | hanti
  · obtain ⟨e⟩ := hAll orderA
    have he : @StrictMono V U orderA.toPreorder orderD.toPreorder e := e.strictMono
    exact ⟨pairReorderEmbedding A B orderA orderA oldB orderB ((f.comp j).comp e)
      (hmono.comp he)⟩
  · let reversed : LinearOrder V := @OrderDual.instLinearOrder V orderA
    obtain ⟨e⟩ := hAll reversed
    have he : @StrictMono V U reversed.toPreorder orderD.toPreorder e := e.strictMono
    have hcomp : @StrictMono V W orderA.toPreorder orderB.toPreorder ((f.comp j).comp e) := by
      intro x y hxy
      exact hanti (he hxy)
    exact ⟨pairReorderEmbedding A B reversed orderA oldB orderB ((f.comp j).comp e) hcomp⟩

end

end Hypertournaments.Affine
