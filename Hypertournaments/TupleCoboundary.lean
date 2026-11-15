import Hypertournaments.LocalTypes
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Intrinsic unsigned coboundaries on injective tuples

No order or symmetry is imposed on a tuple function. Deleting two coordinates
in either order gives the same remaining tuple, so its unsigned coboundary
squares to zero in characteristic two.
-/

namespace Hypertournaments

universe u v

/-- Unsigned simplex coboundary on actual injective ordered tuples. -/
def tupleCoboundary {n : ℕ} {V : Type u}
    (φ : (Fin n ↪ V) → ZMod 2) (f : Fin (n + 1) ↪ V) : ZMod 2 :=
  ∑ i : Fin (n + 1), φ (facet f i)

@[simp] theorem tupleCoboundary_zero {n : ℕ} {V : Type u} (f : Fin (n + 1) ↪ V) :
    tupleCoboundary (fun _ : Fin n ↪ V => 0) f = 0 := by
  simp only [tupleCoboundary, Finset.sum_const_zero]

theorem tupleCoboundary_add {n : ℕ} {V : Type u}
    (φ ψ : (Fin n ↪ V) → ZMod 2) (f : Fin (n + 1) ↪ V) :
    tupleCoboundary (fun t => φ t + ψ t) f = tupleCoboundary φ f + tupleCoboundary ψ f := by
  simp only [tupleCoboundary, Finset.sum_add_distrib]

/-- Deletion commutes with every vertex injection, with no order restriction. -/
theorem tupleCoboundary_naturality {n : ℕ} {V : Type u} {W : Type v}
    (φ : (Fin n ↪ W) → ZMod 2) (e : V ↪ W) (f : Fin (n + 1) ↪ V) :
    tupleCoboundary (fun t => φ (t.trans e)) f = tupleCoboundary φ (f.trans e) := rfl

/-- Intrinsic δ²=0, including arity zero and empty carriers. The fixed-point-free
involution exchanges the two deleted coordinates. -/
theorem tupleCoboundary_tupleCoboundary_zero {n : ℕ} {V : Type u}
    (φ : (Fin n ↪ V) → ZMod 2) (f : Fin (n + 2) ↪ V) :
    tupleCoboundary (tupleCoboundary φ) f = 0 := by
  let flip : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  let value : Fin (n + 2) × Fin (n + 1) → ZMod 2 :=
    fun p => φ (facet (facet f p.1) p.2)
  have hfacet (p : Fin (n + 2) × Fin (n + 1)) :
      facet (facet f (flip p).1) (flip p).2 = facet (facet f p.1) p.2 := by
    ext k
    exact congrArg f (Fin.succAbove_succAbove_succAbove_predAbove p.1 p.2 k)
  have hvalue (p : Fin (n + 2) × Fin (n + 1)) : value (flip p) = value p :=
    congrArg φ (hfacet p)
  change (∑ i : Fin (n + 2), ∑ j : Fin (n + 1), value (i, j)) = 0
  rw [← Fintype.sum_prod_type]
  apply Finset.sum_ninvolution flip
  · intro p
    rw [hvalue]
    simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (value p)
  · intro p _ hp
    exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst hp)
  · intro p
    exact Finset.mem_univ _
  · intro p
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove p.1 p.2
    · exact Fin.predAbove_predAbove_succAbove p.1 p.2

end Hypertournaments
