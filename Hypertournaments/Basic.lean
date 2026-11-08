import Mathlib

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

end Hypertournaments
