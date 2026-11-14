import Hypertournaments.CyclicAmalgamation
import Hypertournaments.RamseyLanguage
import CCO.UnaryHN.OrderedAmbient
import Mathlib.Tactic.Ext

/-!
# Ramsey expansions of finite cyclic orders

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the introduction's compatible-linear-order expansion of cyclic orders.
The expanded class is equivalent to finite linear orders. The existing
pinned pure-order Ramsey theorem supplies the witness directly.
-/

namespace Hypertournaments.Ramsey

universe v w

open StructuralRamsey
open StructuralRamsey.Structure

/-- Compatible linear orders, rather than arbitrary free orders, are named. -/
def compatibleCyclicExpansionClass {V : Type v}
    (C : Structure (orderedLanguage 3) V) : Prop :=
  Finite V ∧ ∃ (A : Hyper 3 V) (order : LinearOrder V),
    A.CircularCompatible (@LinearOrder.toCircularOrder V order) ∧
      C = toOrderedNative A order

private def cyclicPureLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Empty
  relArity R := nomatch R
  funcArity F := nomatch F

private def cyclicPureModel (V : Type v) : Structure cyclicPureLanguage V where
  rel R := nomatch R
  func F := nomatch F

private def cyclicPureOrdered {V : Type v} (order : LinearOrder V) :
    Structure cyclicPureLanguage.withLinearOrder V :=
  @Structure.withLinearOrder cyclicPureLanguage V (cyclicPureModel V) order.toLT

private theorem cyclicPureModel_unique {V : Type v} (C : Structure cyclicPureLanguage V) :
    C = cyclicPureModel V := by
  cases C with
  | mk rel func =>
    have hr : rel = (cyclicPureModel V).rel := funext fun R => nomatch R
    have hf : func = (cyclicPureModel V).func := funext fun F => nomatch F
    cases hr
    cases hf
    rfl

private theorem cyclicPureOrdered_mem {V : Type v} (order : LinearOrder V) :
    CCO.UnaryHN.Native.AllOrderedModels cyclicPureLanguage (cyclicPureOrdered order) := by
  refine ⟨cyclicPureModel V, order, ?_, rfl⟩
  intro F
  exact nomatch F

private def forgetCyclicOrderEmbedding {V W : Type v}
    (A : Hyper 3 V) (B : Hyper 3 W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) :
    Embedding (cyclicPureOrdered orderA) (cyclicPureOrdered orderB) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    cases R with
    | inl R => exact nomatch R
    | inr _ => exact e.map_rel_iff (.inr ()) t
  map_func F := nomatch F

private def liftCyclicOrderEmbedding {V W : Type v}
    (A : Hyper 3 V) (B : Hyper 3 W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (hA : A.CircularCompatible (@LinearOrder.toCircularOrder V orderA))
    (hB : B.CircularCompatible (@LinearOrder.toCircularOrder W orderB))
    (e : Embedding (cyclicPureOrdered orderA) (cyclicPureOrdered orderB)) :
    Embedding (toOrderedNative A orderA) (toOrderedNative B orderB) := by
  let : LinearOrder V := orderA
  let : LinearOrder W := orderB
  let eo : V ↪o W := OrderEmbedding.ofStrictMono e e.strictMono
  exact orderedEmbedding A B eo
    (preserves_circularCompatible_of_strictMono hA hB eo.toEmbedding eo.strictMono)

/-- An actual finite Ramsey witness naming both the ternary orientation
and a compatible order, for every finite nonempty colour palette. -/
theorem exists_cyclic_ramsey_witness {V W : Type v} [Finite V] [Finite W]
    (A : Hyper 3 V) (B : Hyper 3 W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (hA : A.CircularCompatible (@LinearOrder.toCircularOrder V orderA))
    (hB : B.CircularCompatible (@LinearOrder.toCircularOrder W orderB))
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper 3 X) (order : LinearOrder X),
      D.CircularCompatible (@LinearOrder.toCircularOrder X order) ∧
        Structure.Arrow (toOrderedNative A orderA) (toOrderedNative B orderB)
          (toOrderedNative D order) κ := by
  obtain ⟨X, hX, C, hC, arrow⟩ :=
    CCO.UnaryHN.Native.allOrderedModels_ramsey cyclicPureLanguage
      (cyclicPureOrdered orderA) (cyclicPureOrdered orderB)
      (cyclicPureOrdered_mem orderA) (cyclicPureOrdered_mem orderB) κ
  rcases hC with ⟨old, order, _hold, rfl⟩
  rw [cyclicPureModel_unique old] at arrow
  let : Finite X := hX
  let D : Hyper 3 X := @Hyper.ofCircularOrder X (@LinearOrder.toCircularOrder X order)
  have hD : D.CircularCompatible (@LinearOrder.toCircularOrder X order) :=
    Hyper.ofCircularOrder_circularCompatible _
  refine ⟨X, hX, D, order, hD, ?_⟩
  intro χ
  let χ' : Embedding (cyclicPureOrdered orderA) (cyclicPureOrdered order) → κ :=
    fun e => χ (liftCyclicOrderEmbedding A D orderA order hA hD e)
  obtain ⟨f, hf⟩ := arrow χ'
  refine ⟨liftCyclicOrderEmbedding B D orderB order hB hD f, ?_⟩
  intro e₁ e₂
  have hh := hf (forgetCyclicOrderEmbedding A B orderA orderB e₁)
    (forgetCyclicOrderEmbedding A B orderA orderB e₂)
  have he (e : Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) :
      liftCyclicOrderEmbedding A D orderA order hA hD
          (f.comp (forgetCyclicOrderEmbedding A B orderA orderB e)) =
        (liftCyclicOrderEmbedding B D orderB order hB hD f).comp e := by
    apply Embedding.ext
    intro x
    rfl
  change χ (liftCyclicOrderEmbedding A D orderA order hA hD
      (f.comp (forgetCyclicOrderEmbedding A B orderA orderB e₁))) =
    χ (liftCyclicOrderEmbedding A D orderA order hA hD
      (f.comp (forgetCyclicOrderEmbedding A B orderA orderB e₂))) at hh
  simpa only [he] using hh

/-- The full native class of finite cyclic orders with compatible linear
orders is Ramsey. Both named relations are preserved and reflected. -/
theorem cyclic_expansions_ramsey :
    CCO.UnaryHN.Native.Ramsey.{0,v,w} compatibleCyclicExpansionClass := by
  intro V W _ _ A B hA hB κ _ _
  rcases hA with ⟨hV, AA, orderA, hA, rfl⟩
  rcases hB with ⟨hW, BB, orderB, hB, rfl⟩
  let : Finite V := hV
  let : Finite W := hW
  obtain ⟨X, hX, D, order, hD, arrow⟩ :=
    exists_cyclic_ramsey_witness AA BB orderA orderB hA hB κ
  exact ⟨X, hX, toOrderedNative D order, ⟨hX, D, order, hD, rfl⟩, arrow⟩

end Hypertournaments.Ramsey
