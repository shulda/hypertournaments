import Hypertournaments.RamseyLanguage
import Hypertournaments.PairAmalgamation
import CCO.UnaryHN.OrderedAmbient

/-!
# Native hereditary and strong-amalgamation obligations

The class contains actual finite ordered hypertournaments on their whole
carriers. The native strong-amalgamation field includes all spans over empty
bases and does not assume membership of the base in advance.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- A full native embedding into an encoded model reconstructs the entire
source model, with its order pulled back along the embedding. -/
theorem ordered_source_of_embedding {n : ℕ} {V W : Type v}
    (C : Structure (orderedLanguage n) V) (A : Hyper n W) (oW : LinearOrder W)
    (e : Embedding C (toOrderedNative A oW)) :
    ∃ order : LinearOrder V, C = toOrderedNative (A.pullback e.toFunctionEmbedding) order := by
  let : LinearOrder W := oW
  let order : LinearOrder V := LinearOrder.lift' e e.injective
  refine ⟨order, native_ext ?_⟩
  intro R t
  cases R with
  | inl R =>
    change C.rel (.inl R) t ↔ (A.pullback e.toFunctionEmbedding).Relation t
    exact (e.map_rel_iff (.inl R) t).symm.trans (A.relation_pullback e.toFunctionEmbedding t).symm
  | inr R =>
    exact (e.map_rel_iff (.inr R) t).symm

/-- Heredity against the actual full native embedding interface. -/
theorem orderedOmissionClass_hereditary {n : ℕ} (family : ForbiddenFamily n) :
    CCO.UnaryHN.Native.Hereditary (orderedOmissionClass.{v} family) := by
  intro V W C D hD e
  rcases hD with ⟨hW, A, oW, hA, rfl⟩
  let : Finite W := hW
  obtain ⟨order, hC⟩ := ordered_source_of_embedding C A oW e
  exact ⟨Finite.of_injective e e.injective, A.pullback e.toFunctionEmbedding,
    order, omits_pullback hA e.toFunctionEmbedding, hC⟩

/-- Every member is a whole-carrier globally ordered native model. -/
theorem orderedOmissionClass_sub_ambient {n : ℕ} (family : ForbiddenFamily n)
    {V : Type v} (C : Structure (orderedLanguage n) V)
    (hC : orderedOmissionClass family C) :
    CCO.UnaryHN.Native.AllOrderedModels (orientationLanguage n) C := by
  rcases hC with ⟨_, A, order, _, rfl⟩
  refine ⟨toNative A, order, ?_, rfl⟩
  intro F
  exact nomatch F

theorem orderedOmissionClass_allIrreducible {n : ℕ} (family : ForbiddenFamily n) :
    CCO.UnaryHN.Native.AllIrreducible (orderedOmissionClass.{v} family) := by
  rintro V C ⟨_, A, order, _, rfl⟩
  exact @CCO.UnaryHN.Native.withLinearOrder_irreducible (orientationLanguage n) V
    (toNative A) order

/-- All native finiteness, heredity, singleton and exact-overlap SAP obligations
are discharged by the actual ordered pair-cancelling amalgamation theorem. -/
theorem orderedOmissionClass_finiteHereditarySAP {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    CCO.UnaryHN.Native.FiniteHereditarySAP (orderedOmissionClass.{v} family) where
  finite C hC := hC.1
  singleton C _ := singletonValued C
  hereditary := orderedOmissionClass_hereditary family
  strong := by
    intro H V W Root Left Right hLeft hRight sL sR
    have hRoot := orderedOmissionClass_hereditary family hLeft sL
    rcases hRoot with ⟨hH, AA, oH, hAA, rfl⟩
    rcases hLeft with ⟨hV, BB, oV, hBB, rfl⟩
    rcases hRight with ⟨hW, CC, oW, hCC, rfl⟩
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
    obtain ⟨order, D, hD, hi, hj, hiOrder, hjOrder⟩ :=
      pair_cancelling_ordered_strong_span hn family hpc AA BB CC f g hf hg hBB hCC
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
      ⟨inferInstance, D, order, hD, rfl⟩, ei, ej, ?_, ?_⟩
    · intro a
      exact FiniteStrongSpan.commutes f.toEmbedding g.toEmbedding a
    · intro x y hxy
      obtain ⟨a, ha, hb⟩ := (FiniteStrongSpan.overlap f.toEmbedding g.toEmbedding x y).mp hxy
      exact ⟨a, ha.symm, hb.symm⟩

end Hypertournaments.Ramsey
