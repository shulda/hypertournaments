import Hypertournaments.RamseyCompletion
import Hypertournaments.RamseyClass
import CCO.UnaryHN.IteratedTransfer

/-!
# Ramsey theorem for the freely ordered pair-cancelling omission classes

The arbitrary-relational same-carrier completion supplies the genuine HN
local-finiteness condition. The small-substructure test is unnecessary, so
cutoff one works. All language, class, SAP and completion inputs are discharged.
Source: article pin 919349e7eceed3c7fa0ed126a337c6fae6624704, `thm:Ramsey`.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Genuine original HN local finiteness with a cutoff of one. -/
theorem orderedOmissionClass_locallyFinite {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    CCO.UnaryHN.Native.LocallyFinite (orderedOmissionClass.{v} family)
      (CCO.UnaryHN.Native.AllOrderedModels (orientationLanguage n)) := by
  intro P _ C₀ hC₀
  refine ⟨1, ?_⟩
  intro V _ C _hSingleton hProjection hIrr _hSmall
  obtain ⟨p, hp⟩ := hProjection
  rcases hC₀ with ⟨old, orderP, _, rfl⟩
  let : LinearOrder P := orderP
  have hpart : ∀ x y, C.rel (.inr ()) ![x, y] → p x < p y := by
    intro x y hxy
    exact hp.1.1 (.inr ()) ![x, y] hxy
  obtain ⟨order, hExt⟩ := Structure.exists_linearOrder_extension C p hpart
  obtain ⟨D, hD, hHE⟩ := exists_native_strong_completion hn family hpc C hIrr order hExt
  exact ⟨V, inferInstance, toOrderedNative D order,
    ⟨inferInstance, D, order, hD, rfl⟩, id, hHE⟩

/-- The freely ordered omission class is Ramsey for every finite nonempty
colour palette. The only mathematical family hypothesis is pair-cancellation. -/
theorem pair_cancelling_ordered_ramsey {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    CCO.UnaryHN.Native.Ramsey.{0,v,w} (orderedOmissionClass.{v} family) := by
  apply CCO.UnaryHN.Native.original_unary_locally_finite_ramsey
    (R := CCO.UnaryHN.Native.AllOrderedModels (orientationLanguage n))
  · intro F
    exact nomatch F
  · exact orderedOmissionClass_finiteHereditarySAP hn family hpc
  · exact orderedOmissionClass_sub_ambient family
  · exact CCO.UnaryHN.Native.orderedClass_allIrreducible (fun C => C.SingletonValued)
  · exact CCO.UnaryHN.Native.allOrderedModels_ramsey (orientationLanguage n)
  · exact orderedOmissionClass_locallyFinite hn family hpc

/-- Explicit witness formulation using the original Hyper structures and
chosen free orders. The arrow uses the full induced relational embeddings. -/
theorem exists_ordered_ramsey_witness {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {V W : Type v} [Finite V] [Finite W]
    (A : Hyper n V) (B : Hyper n W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (hA : Omits family A) (hB : Omits family B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper n X) (order : LinearOrder X),
      Omits family D ∧ Structure.Arrow (toOrderedNative A orderA)
        (toOrderedNative B orderB) (toOrderedNative D order) κ := by
  obtain ⟨X, hX, C, hC, hArrow⟩ := pair_cancelling_ordered_ramsey hn family hpc
    (toOrderedNative A orderA) (toOrderedNative B orderB)
    ⟨inferInstance, A, orderA, hA, rfl⟩ ⟨inferInstance, B, orderB, hB, rfl⟩ κ
  rcases hC with ⟨_, D, order, hD, rfl⟩
  exact ⟨X, hX, D, order, hD, hArrow⟩

end Hypertournaments.Ramsey
