import Hypertournaments.CircularCut
import Hypertournaments.EPPAExtension
import Hypertournaments.FiniteHyperClass
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Circular
import Mathlib.Order.Preorder.Finite

/-!
# Cyclic orders do not have EPPA within the cyclic class

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the finite cyclic-order discussion following `cor:even-no-eppa`.
The proof uses one actual two-point partial isomorphism fixing one vertex.
The obstruction concerns cyclic witnesses, with no restriction asserted
on unrestricted ternary EPPA witnesses.
-/

universe u v

namespace Hypertournaments

/-- A finite cyclic-order automorphism fixing one vertex fixes every vertex. -/
theorem Hyper.Aut.eq_one_of_isCyclicOrder {V : Type u} [Finite V]
    {A : Hyper 3 V} (g : A.Aut) (hA : A.IsCyclicOrder) (p : V)
    (hp : (g : Equiv.Perm V) p = p) : g = 1 := by
  obtain ⟨order, horder⟩ := hA
  let : CircularOrder V := order
  have hg := (preserves_iff_sbtw order order horder horder
    (g : Equiv.Perm V).toEmbedding).mp g.preserves
  have hm := CircularOrder.cutLinearOrder_strictMono
    (g : Equiv.Perm V).toEmbedding p p hp hg
  let : LinearOrder V := CircularOrder.cutLinearOrder p
  apply Hyper.Aut.ext
  intro x
  exact hm.apply_eq

/-- Every injection from a two-point ternary structure preserves orientations. -/
theorem preserves_ternary_from_two {V : Type u} (P : Hyper 3 (Fin 2))
    (A : Hyper 3 V) (e : Fin 2 ↪ V) : Preserves P A e := by
  intro t
  have hc : 3 ≤ 2 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective t t.injective
  exact (Nat.not_succ_le_self 2 hc).elim

/-- A structure with three vertices has no finite EPPA witness within cyclic orders. -/
theorem Hyper.not_isEPPAWitness_cyclic_of_three {V : Type u} {W : Type v}
    (A : Hyper 3 V) (B : Hyper 3 W) (s : Fin 3 ↪ V)
    (hB : B.IsCyclicOrder) (e : V ↪ W) : ¬ A.IsEPPAWitness B e := by
  intro hw
  let : Finite W := hw.finite
  let f : Fin 2 ↪ V := Function.Embedding.embFinTwo
    (s.injective.ne (by decide : (0 : Fin 3) ≠ 1))
  let g : Fin 2 ↪ V := Function.Embedding.embFinTwo
    (s.injective.ne (by decide : (0 : Fin 3) ≠ 2))
  let P := A.pullback f
  obtain ⟨σ, hσ⟩ := hw.extend_isomorphism P f g
    (preserves_ternary_from_two P A f) (preserves_ternary_from_two P A g)
  have hp : (σ : Equiv.Perm W) (e (s 0)) = e (s 0) := by
    simpa only [f, g, Function.Embedding.embFinTwo_apply_zero] using hσ 0
  have hσid := σ.eq_one_of_isCyclicOrder hB (e (s 0)) hp
  have h12 : e (s 1) = e (s 2) := by
    simpa only [hσid, Subgroup.coe_one, Equiv.Perm.one_apply, f, g,
      Function.Embedding.embFinTwo_apply_one] using hσ 1
  exact (by decide : (1 : Fin 3) ≠ 2) (s.injective (e.injective h12))

/-- Cyclic orders, presented on finite ordinals. -/
def cyclicOrderClass : FiniteHyperClass 3 := fun _ => {A | A.IsCyclicOrder}

/-- A concrete cyclic three-vertex structure. -/
noncomputable def cyclicThree : Hyper 3 (Fin 3) :=
  @Hyper.ofCircularOrder (Fin 3) (LinearOrder.toCircularOrder (Fin 3))

theorem cyclicThree_isCyclicOrder : cyclicThree.IsCyclicOrder :=
  ⟨LinearOrder.toCircularOrder (Fin 3),
    Hyper.ofCircularOrder_circularCompatible (LinearOrder.toCircularOrder (Fin 3))⟩

/-- The finite cyclic-order class fails ordinary EPPA. -/
theorem cyclicOrderClass_not_hasEPPA : ¬ ClassHasEPPA cyclicOrderClass := by
  intro h
  obtain ⟨b, B, e, hB, hw⟩ := h 3 cyclicThree cyclicThree_isCyclicOrder
  exact cyclicThree.not_isEPPAWitness_cyclic_of_three B
    (Function.Embedding.refl _) hB e hw

end Hypertournaments
