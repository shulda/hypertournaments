import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Ext

/-!
# Finite arity hypertournaments: an order-free encoding

An orientation is a Boolean choice on each injective ordered n-tuple.
Transposing two coordinates reverses the choice. No linear order of
the ambient vertex set is part of the mathematical structure.

This module contains definitions, not the negative classification theorem.
-/

universe u v

namespace Hypertournaments

/-- An n-hypertournament on V, specified on injective n-tuples.
The swap law expresses alternating orientations. -/
structure Hyper (n : ℕ) (V : Type u) where
  orient : (Fin n ↪ V) → Bool
  swap_flip : ∀ (f : Fin n ↪ V) (i j : Fin n), i ≠ j →
    orient ((Equiv.swap i j).toEmbedding.trans f) = !(orient f)

/-- A vertex embedding preserving every oriented injective n-tuple. -/
def Preserves {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) (f : V ↪ W) : Prop :=
  ∀ t : Fin n ↪ V, B.orient (t.trans f) = A.orient t

/-- Pull back/restrict an intrinsic hypertournament along an injection. -/
def Hyper.pullback {n : ℕ} {V : Type u} {W : Type v}
    (B : Hyper n W) (f : V ↪ W) : Hyper n V where
  orient := fun t => B.orient (t.trans f)
  swap_flip := by
    intro t i j hij
    exact B.swap_flip (t.trans f) i j hij

/-- Preservation means agreement with the intrinsic pullback orientation. -/
theorem preserves_iff_pullback {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) (f : V ↪ W) :
    Preserves A B f ↔ ∀ t : Fin n ↪ V, A.orient t = (B.pullback f).orient t := by
  constructor
  · intro h t
    exact (h t).symm
  · intro h t
    exact (h t).symm

/-- Alternation under an arbitrary permutation of tuple coordinates:
a permutation preserves orientation exactly when its sign is +1. -/
theorem Hyper.orient_perm {n : ℕ} {V : Type u}
    (A : Hyper n V) (f : Fin n ↪ V) (σ : Equiv.Perm (Fin n)) :
    A.orient (σ.toEmbedding.trans f) =
      if σ.sign = (1 : ℤˣ) then A.orient f else !(A.orient f) := by
  refine Equiv.Perm.swap_induction_on' σ ?_ ?_
  · have h : ((1 : Equiv.Perm (Fin n)).toEmbedding.trans f) = f := by
      ext x
      rfl
    simp [h]
  · intro τ i j hij ih
    have hswap := A.swap_flip (τ.toEmbedding.trans f) i j hij
    have hcomp :
        ((τ * Equiv.swap i j).toEmbedding.trans f) =
          (Equiv.swap i j).toEmbedding.trans (τ.toEmbedding.trans f) := by
      ext x
      rfl
    rw [hcomp, hswap, ih, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap hij]
    rcases Int.units_eq_one_or τ.sign with h | h <;> simp [h, Units.ext_iff]

end Hypertournaments
