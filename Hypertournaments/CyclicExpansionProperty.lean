import Hypertournaments.CyclicAmalgamation
import Hypertournaments.AllOrderHost
import Hypertournaments.RamseyLanguage

/-!
# The expansion property for compatible cyclic-order presentations

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the introduction's compatible linear-order expansion of finite cyclic orders.
Every two compatible linear presentations of the same finite cyclic order
are isomorphic as ordered orientation structures. The original cyclic order
itself therefore witnesses the expansion property, including on an empty carrier.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Any compatible linear presentation embeds into every other compatible
linear presentation of the same finite intrinsic cyclic order. -/
theorem cyclic_compatible_expansions_embed
    {V : Type v} [Finite V] (A : Hyper 3 V)
    (orderA orderB : LinearOrder V)
    (hA : A.CircularCompatible (@LinearOrder.toCircularOrder V orderA))
    (hB : A.CircularCompatible (@LinearOrder.toCircularOrder V orderB)) :
    Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative A orderB)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e : @OrderIso V V orderA.toLE orderB.toLE := orderChange orderA orderB
  have hmono : @StrictMono V V orderA.toPreorder orderB.toPreorder e :=
    @OrderIso.strictMono V V orderA.toPreorder orderB.toPreorder e
  have he : Preserves A A e.toEquiv.toEmbedding :=
    @preserves_circularCompatible_of_strictMono V V orderA orderB A A hA hB
      e.toEquiv.toEmbedding hmono
  exact ⟨@orderedEmbedding 3 V V orderA orderB A A
    (@OrderIso.toOrderEmbedding V V orderA.toLE orderB.toLE e) he⟩

/-- The finite cyclic-order class has the expansion property for compatible
linear presentations. The witness is fixed before both orders are chosen. -/
theorem cyclic_expansion_property
    {V : Type v} [Finite V] (A : Hyper 3 V) (hA : A.IsCyclicOrder) :
    ∃ (W : Type v) (_ : Finite W) (B : Hyper 3 W), B.IsCyclicOrder ∧
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        A.CircularCompatible (@LinearOrder.toCircularOrder V orderA) →
        B.CircularCompatible (@LinearOrder.toCircularOrder W orderB) →
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) := by
  refine ⟨V, inferInstance, A, hA, ?_⟩
  intro orderA orderB horderA horderB
  exact cyclic_compatible_expansions_embed A orderA orderB horderA horderB

end Hypertournaments.Ramsey
