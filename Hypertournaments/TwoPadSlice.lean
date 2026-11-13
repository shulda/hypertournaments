import Mathlib.Tactic.Ext
import Hypertournaments.TwoPadIntrinsic

/-!
# Recovering an intrinsic lower-arity orientation from two pad vertices

Let D be an (n+2)-hypertournament, g an embedding of the proposed old
vertex type into D, and p,q two distinct vertices outside the image
of g. On any injective old n-tuple f we read the orientation of the
(n+2)-tuple (p,q,g(f(0)),...,g(f(n-1))).

The resulting orientation is alternating, because every old coordinate
permutation lifts to an ambient permutation fixing the first two
coordinates and preserving the sign. This construction uses no
linear order on the ambient amalgam, so it remains valid when the
two newly added source vertices are identified.

Admissibility of the recovered structure, for a particular local
type class, is a separate statement handled by packet reflection.
-/

namespace Hypertournaments

/-- Reordering the old coordinates of an embedding does not change
its range. A vertex outside the old range remains outside it. -/
theorem not_mem_range_reordered
    {n : ℕ} {V : Type*}
    (f : Fin n ↪ V) (v : V) (hv : v ∉ Set.range f)
    (σ : Equiv.Perm (Fin n)) :
    v ∉ Set.range (σ.toEmbedding.trans f) := by
  rintro ⟨i, hi⟩
  exact hv ⟨σ i, hi⟩

/-- The entire two-pad tuple is natural under arbitrary
permutations of its old coordinates. -/
theorem twoPadTuple_reordered
    {n : ℕ} {V : Type*}
    (f : Fin n ↪ V) (p q : V)
    (hp : p ∉ Set.range f) (hq : q ∉ Set.range f)
    (hpq : p ≠ q) (σ : Equiv.Perm (Fin n)) :
    twoPadTuple (σ.toEmbedding.trans f) p q
      (not_mem_range_reordered f p hp σ)
      (not_mem_range_reordered f q hq σ) hpq =
      (twoPadLiftPerm σ).toEmbedding.trans
        (twoPadTuple f p q hp hq hpq) := by
  ext k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) k
  · simp
  · simp
  · simp

/-- A vertex excluded from the whole old embedded vertex set is
excluded from every injective tuple inside that set. -/
theorem not_mem_range_restricted
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (f : Fin n ↪ W)
    (v : V) (hv : v ∉ Set.range g) :
    v ∉ Set.range (f.trans g) := by
  rintro ⟨i, hi⟩
  exact hv ⟨f i, hi⟩

/-- Prefix two fixed pads to an arbitrary old tuple, after embedding
the old underlying vertex set into the ambient hypertournament. -/
def twoPadSliceTuple
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (f : Fin n ↪ W) :
    Fin (n + 2) ↪ V :=
  twoPadTuple (f.trans g) p q
    (not_mem_range_restricted g f p hp)
    (not_mem_range_restricted g f q hq) hpq

/-- Relabeling old coordinates commutes with forming the two-pad
tuple, also after mapping old vertices into the ambient structure. -/
theorem twoPadSliceTuple_reordered
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (f : Fin n ↪ W)
    (σ : Equiv.Perm (Fin n)) :
    twoPadSliceTuple g p q hp hq hpq (σ.toEmbedding.trans f) =
      (twoPadLiftPerm σ).toEmbedding.trans
        (twoPadSliceTuple g p q hp hq hpq f) := by
  ext k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) k
  · simp [twoPadSliceTuple]
  · simp [twoPadSliceTuple]
  · simp [twoPadSliceTuple]

/-- The intrinsic n-hypertournament obtained from two fixed pad
vertices of an (n+2)-hypertournament. All embeddings and orders
of the old vertices are permitted. -/
def Hyper.twoPadSlice
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) : Hyper n W where
  orient := fun f => D.orient (twoPadSliceTuple g p q hp hq hpq f)
  swap_flip := by
    intro f i j hij
    change D.orient (twoPadSliceTuple g p q hp hq hpq
        ((Equiv.swap i j).toEmbedding.trans f)) =
      !(D.orient (twoPadSliceTuple g p q hp hq hpq f))
    rw [twoPadSliceTuple_reordered]
    have hsign :
        (twoPadLiftPerm (Equiv.swap i j)).sign ≠ (1 : ℤˣ) := by
      rw [twoPadLiftPerm_sign, Equiv.Perm.sign_swap hij]
      decide
    rw [D.orient_perm]
    simp [hsign]

/-- Recovery is simply the ambient orientation evaluated on the
explicit tuple with two leading pads. -/
theorem Hyper.twoPadSlice_orient
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (f : Fin n ↪ W) :
    (D.twoPadSlice g p q hp hq hpq).orient f =
      D.orient (twoPadSliceTuple g p q hp hq hpq f) := rfl

end Hypertournaments
