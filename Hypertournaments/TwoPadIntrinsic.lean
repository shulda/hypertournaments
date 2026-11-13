import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.GroupTheory.Perm.Fin
import Hypertournaments.TwoPadProfiles

/-!
# Intrinsic two-pad tuples

The non-amalgamation reflection must read an n-orientation inside an
(n+2)-orientation without choosing an order on a possible amalgam.
We construct the actual injective (n+2)-tuple by prepending two fixed
distinct pad vertices. The old vertices may be in an arbitrary order.

This file establishes the coordinate identities and the odd-sign
permutation of the two-pad tuple induced by swapping any pair of old
coordinates. It makes no claim about amalgamation or admissibility.
-/

namespace Hypertournaments

/-- A vertex outside the range of a tuple, and distinct from its
new first entry, remains outside the extended tuple. -/
theorem not_mem_range_cons_of_not_mem
    {n : ℕ} {V : Type*}
    (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f)
    (hq : q ∉ Set.range f)
    (hpq : p ≠ q) :
    p ∉ Set.range (Fin.Embedding.cons f hq) := by
  intro h
  have hh : p = q ∨ p ∈ Set.range f := by
    simpa only [Fin.Embedding.coe_cons, Fin.range_cons, Set.mem_insert_iff]
      using h
  exact hh.elim hpq hp

/-- Prepend two distinct vertices to an arbitrary injective old
n-tuple. The hypotheses say both pads lie outside the old tuple. -/
def twoPadTuple
    {n : ℕ} {V : Type*}
    (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f)
    (hq : q ∉ Set.range f)
    (hpq : p ≠ q) :
    Fin (n + 2) ↪ V :=
  Fin.Embedding.cons (Fin.Embedding.cons f hq)
    (not_mem_range_cons_of_not_mem f p q hp hq hpq)

@[simp]
theorem twoPadTuple_zero
    {n : ℕ} {V : Type*} (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f) (hq : q ∉ Set.range f)
    (hpq : p ≠ q) :
    twoPadTuple f p q hp hq hpq 0 = p := by
  simp [twoPadTuple, Fin.Embedding.cons]

@[simp]
theorem twoPadTuple_one
    {n : ℕ} {V : Type*} (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f) (hq : q ∉ Set.range f)
    (hpq : p ≠ q) :
    twoPadTuple f p q hp hq hpq 1 = q := by
  simp [twoPadTuple, Fin.Embedding.cons, Fin.cons_succ]

@[simp]
theorem twoPadTuple_old
    {n : ℕ} {V : Type*} (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f) (hq : q ∉ Set.range f)
    (hpq : p ≠ q) (i : Fin n) :
    twoPadTuple f p q hp hq hpq i.succ.succ = f i := by
  simp [twoPadTuple, Fin.Embedding.cons, Fin.cons_succ]

/-- Extend a permutation of the old n coordinates by two fixed
coordinates at the front. -/
def twoPadLiftPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin.symm
    (0, Equiv.Perm.decomposeFin.symm (0, σ))

@[simp]
theorem twoPadLiftPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    twoPadLiftPerm σ 0 = 0 := by
  simp [twoPadLiftPerm]

@[simp]
theorem twoPadLiftPerm_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    twoPadLiftPerm σ 1 = 1 := by
  simp [twoPadLiftPerm]

@[simp]
theorem twoPadLiftPerm_old {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    twoPadLiftPerm σ i.succ.succ = (σ i).succ.succ := by
  simp [twoPadLiftPerm]

/-- Adding two fixed initial coordinates preserves the sign of
an arbitrary permutation on the old coordinates. -/
theorem twoPadLiftPerm_sign {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    (twoPadLiftPerm σ).sign = σ.sign := by
  simp [twoPadLiftPerm, Equiv.Perm.decomposeFin.symm_sign]

end Hypertournaments
