import Mathlib.Data.Fin.VecNotation
import Hypertournaments.UnrestrictedAmalgamation
import Hypertournaments.RamseyCompletion
import Hypertournaments.RamseyClass
import CCO.UnaryHN.IteratedTransfer

/-!
# Ramsey theorem for all ordered hypertournaments, including tournaments

For the empty forbidden family every construction is available already in
arity two. The genuine native SAP and arbitrary-relational local completion
inputs are supplied below, so the binary case is part of the actual HN theorem.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-- All native SAP fields for the unrestricted ordered class, for n at least two. -/
theorem unrestricted_orderedOmissionClass_finiteHereditarySAP {n : ℕ} (hn : 2 ≤ n) :
    CCO.UnaryHN.Native.FiniteHereditarySAP (orderedOmissionClass.{v} (emptyForbiddenFamily n)) where
  finite C hC := hC.1
  singleton C _ := singletonValued C
  hereditary := orderedOmissionClass_hereditary (emptyForbiddenFamily n)
  strong := by
    intro H V W Root Left Right hLeft hRight sL sR
    have hRoot := orderedOmissionClass_hereditary (emptyForbiddenFamily n) hLeft sL
    rcases hRoot with ⟨hH, AA, oH, _hAA, rfl⟩
    rcases hLeft with ⟨hV, BB, oV, _hBB, rfl⟩
    rcases hRight with ⟨hW, CC, oW, _hCC, rfl⟩
    let : Finite H := hH
    let : Finite V := hV
    let : Finite W := hW
    let : LinearOrder H := oH
    let : LinearOrder V := oV
    let : LinearOrder W := oW
    let f : H ↪o V := OrderEmbedding.ofStrictMono sL
      (strictMono_of_orderedEmbedding AA BB sL)
    let g : H ↪o W := OrderEmbedding.ofStrictMono sR
      (strictMono_of_orderedEmbedding AA CC sR)
    have hf : Preserves AA BB f.toEmbedding := preserves_of_orderedEmbedding AA BB oH oV sL
    have hg : Preserves AA CC g.toEmbedding := preserves_of_orderedEmbedding AA CC oH oW sR
    obtain ⟨order, D, hi, hj, hiOrder, hjOrder⟩ :=
      unrestricted_ordered_strong_span hn AA BB CC f g hf hg
    let X := FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding
    let i : @OrderEmbedding V X oV.toLE order.toLE :=
      @OrderEmbedding.ofStrictMono V X oV order.toPreorder
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) hiOrder
    let j : @OrderEmbedding W X oW.toLE order.toLE :=
      @OrderEmbedding.ofStrictMono W X oW order.toPreorder
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) hjOrder
    let ei := @orderedEmbedding n V X oV order BB D i hi
    let ej := @orderedEmbedding n W X oW order CC D j hj
    refine ⟨X, inferInstance, toOrderedNative D order,
      ⟨inferInstance, D, order, omits_emptyForbiddenFamily D, rfl⟩, ei, ej, ?_, ?_⟩
    · intro a
      exact FiniteStrongSpan.commutes f.toEmbedding g.toEmbedding a
    · intro x y hxy
      obtain ⟨a, ha, hb⟩ := (FiniteStrongSpan.overlap f.toEmbedding g.toEmbedding x y).mp hxy
      exact ⟨a, ha.symm, hb.symm⟩

/-- Actual same-carrier completion of arbitrary relational inputs, in arity two
as well as higher arities; the old irreducible pieces supply orientation consistency. -/
theorem exists_unrestricted_native_strong_completion {n : ℕ} (hn : 2 ≤ n)
    {V : Type v} [Finite V] (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass (emptyForbiddenFamily n)) C)
    (order : LinearOrder V)
    (hExt : ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt V order.toLT x y) :
    ∃ D : Hyper n V, Omits (emptyForbiddenFamily n) D ∧
      C.IsEHNHomomorphismEmbedding (toOrderedNative D order) id := by
  classical
  let : LinearOrder V := order
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨D, hPD, hD⟩ := exists_pair_cancelling_completion hn
    (partialOrientation (emptyForbiddenFamily n) C hIrr) (missingPairs C) (missingPairs_distinct C)
    (partial_cliqueDomain (emptyForbiddenFamily n) C hIrr)
    (emptyForbiddenFamily n) (emptyForbiddenFamily_pairCancelling n)
    (partial_omits (emptyForbiddenFamily n) (emptyForbiddenFamily_pairCancelling n) C hIrr)
  exact ⟨D, hD, nativeHE_of_completion (emptyForbiddenFamily n) C hIrr order hExt D hPD⟩

/-- Original HN local finiteness, with cutoff one, for all hypertournaments. -/
theorem unrestricted_orderedOmissionClass_locallyFinite {n : ℕ} (hn : 2 ≤ n) :
    CCO.UnaryHN.Native.LocallyFinite (orderedOmissionClass.{v} (emptyForbiddenFamily n))
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
  obtain ⟨D, hD, hHE⟩ := exists_unrestricted_native_strong_completion hn C hIrr order hExt
  exact ⟨V, inferInstance, toOrderedNative D order,
    ⟨inferInstance, D, order, hD, rfl⟩, id, hHE⟩

/-- The actual native Ramsey property for all freely ordered n-hypertournaments,
uniformly for every n at least two and every finite nonempty color palette. -/
theorem unrestricted_ordered_ramsey {n : ℕ} (hn : 2 ≤ n) :
    CCO.UnaryHN.Native.Ramsey.{0,v,w} (orderedOmissionClass.{v} (emptyForbiddenFamily n)) := by
  apply CCO.UnaryHN.Native.original_unary_locally_finite_ramsey
    (R := CCO.UnaryHN.Native.AllOrderedModels (orientationLanguage n))
  · intro F
    exact nomatch F
  · exact unrestricted_orderedOmissionClass_finiteHereditarySAP hn
  · exact orderedOmissionClass_sub_ambient (emptyForbiddenFamily n)
  · exact CCO.UnaryHN.Native.orderedClass_allIrreducible (fun C => C.SingletonValued)
  · exact CCO.UnaryHN.Native.allOrderedModels_ramsey (orientationLanguage n)
  · exact unrestricted_orderedOmissionClass_locallyFinite hn

/-- An explicit unrestricted ordered Ramsey witness. No omission premise is
needed for either input. The displayed omission conclusion is automatically true. -/
theorem exists_unrestricted_ordered_ramsey_witness {n : ℕ} (hn : 2 ≤ n)
    {V W : Type v} [Finite V] [Finite W]
    (A : Hyper n V) (B : Hyper n W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper n X) (order : LinearOrder X),
      Omits (emptyForbiddenFamily n) D ∧ Structure.Arrow (toOrderedNative A orderA)
        (toOrderedNative B orderB) (toOrderedNative D order) κ := by
  obtain ⟨X, hX, C, hC, hArrow⟩ := unrestricted_ordered_ramsey hn
    (toOrderedNative A orderA) (toOrderedNative B orderB)
    ⟨inferInstance, A, orderA, omits_emptyForbiddenFamily A, rfl⟩
    ⟨inferInstance, B, orderB, omits_emptyForbiddenFamily B, rfl⟩ κ
  rcases hC with ⟨_, D, order, hD, rfl⟩
  exact ⟨X, hX, D, order, hD, hArrow⟩

end Hypertournaments.Ramsey
