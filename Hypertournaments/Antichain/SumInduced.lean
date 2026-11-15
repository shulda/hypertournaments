import Hypertournaments.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Hypertournaments induced by sums of tournament edges

Source: Sullivan, `Ultrahomogeneous hypertournaments`,
arXiv:2611.07292v1, Definition 3.5.

The orientation of an ordered tuple is the sum in `ZMod 2` of the
tournament orientations on all its increasing coordinate pairs. This
construction is intrinsic: no order on the vertex set is used.
-/

namespace Hypertournaments.Antichain

universe u v

/-- The usual identification of Boolean values with the two-element field. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_injective : Function.Injective bit := by
  intro b c h
  cases b <;> cases c <;> simp_all [bit]

@[simp] theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> decide

@[simp] theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

/-- Read a field element back as a Boolean. -/
def boolOf (x : ZMod 2) : Bool := decide (x = 1)

@[simp] theorem bit_boolOf (x : ZMod 2) : bit (boolOf x) = x := by
  have h : ∀ x : ZMod 2, bit (boolOf x) = x := by decide +kernel
  exact h x

@[simp] theorem boolOf_bit (b : Bool) : boolOf (bit b) = b := by
  cases b <;> decide

@[simp] theorem boolOf_add_one (x : ZMod 2) : boolOf (x + 1) = !(boolOf x) := by
  apply bit_injective
  simp

/-- A tournament's ordered edge bit, set to zero on the unused diagonal. -/
noncomputable def tournamentBit {V : Type u} (T : Hyper 2 V) (x y : V) : ZMod 2 := by
  classical
  exact if h : x ≠ y then bit (T.orient (Function.Embedding.embFinTwo h)) else 0

theorem tournamentBit_of_ne {V : Type u} (T : Hyper 2 V) {x y : V} (h : x ≠ y) :
    tournamentBit T x y = bit (T.orient (Function.Embedding.embFinTwo h)) := by
  classical
  simp [tournamentBit, h]

theorem tournamentBit_reverse {V : Type u} (T : Hyper 2 V) {x y : V} (h : x ≠ y) :
    tournamentBit T y x = tournamentBit T x y + 1 := by
  classical
  rw [tournamentBit_of_ne T h.symm, tournamentBit_of_ne T h]
  have he : Function.Embedding.embFinTwo h.symm =
      (Equiv.swap (0 : Fin 2) 1).toEmbedding.trans
        (Function.Embedding.embFinTwo h) := by
    ext i
    fin_cases i <;> simp [Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one]
  rw [he, T.swap_flip _ 0 1 (by decide), bit_not]

@[simp] theorem tournamentBit_self {V : Type u} (T : Hyper 2 V) (x : V) :
    tournamentBit T x x = 0 := by
  classical
  simp [tournamentBit]

theorem tournamentBit_preserves {V : Type u} {W : Type v}
    (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W) (he : Preserves T U e)
    (x y : V) : tournamentBit U (e x) (e y) = tournamentBit T x y := by
  classical
  by_cases h : x = y
  · subst y
    simp
  · have h' : e x ≠ e y := fun hxy => h (e.injective hxy)
    rw [tournamentBit_of_ne U h', tournamentBit_of_ne T h]
    have hh : Function.Embedding.embFinTwo h' =
        (Function.Embedding.embFinTwo h).trans e := by
      ext i
      fin_cases i <;> simp [Function.Embedding.embFinTwo_apply_zero,
        Function.Embedding.embFinTwo_apply_one]
    rw [hh, he]

/-- Sum over the two-element subsets of the coordinate set, in coordinate order. -/
noncomputable def pairSum {n : ℕ} {V : Type u} (T : Hyper 2 V)
    (f : Fin n ↪ V) : ZMod 2 :=
  ∑ p ∈ Equiv.Perm.finPairsLT n, tournamentBit T (f p.2) (f p.1)

theorem pairSum_eq_sum {n : ℕ} {V : Type u} (T : Hyper 2 V) (f : Fin n ↪ V) :
    pairSum T f = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then tournamentBit T (f i) (f j) else 0 := by
  classical
  have hp : Equiv.Perm.finPairsLT n =
      Finset.univ.sigma (fun j : Fin n => Finset.univ.filter (fun i : Fin n => i < j)) := by
    ext p
    simp [Equiv.Perm.mem_finPairsLT]
  rw [pairSum, hp, Finset.sum_sigma]
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

/-- Changing a single tuple coordinate changes exactly its incident edge terms. -/
theorem pairSum_exchange {n : ℕ} {V : Type u} (T : Hyper 2 V)
    (f g : Fin n ↪ V) (j : Fin n) (hfg : ∀ i, i ≠ j → f i = g i) :
    pairSum T f + pairSum T g =
      ∑ i ∈ Finset.univ.erase j,
        (tournamentBit T (f j) (f i) + tournamentBit T (g j) (g i)) := by
  classical
  let d (a b : Fin n) := tournamentBit T (f a) (f b) + tournamentBit T (g a) (g b)
  have hd (a b : Fin n) : d a b = d b a := by
    by_cases hab : a = b
    · subst b; rfl
    · have hf : f a ≠ f b := fun h => hab (f.injective h)
      have hg : g a ≠ g b := fun h => hab (g.injective h)
      dsimp [d]
      rw [tournamentBit_reverse T hf, tournamentBit_reverse T hg]
      have hh : ∀ x y : ZMod 2, x + y = (x + 1) + (y + 1) := by decide +kernel
      exact hh _ _
  have hz (a b : Fin n) (ha : a ≠ j) (hb : b ≠ j) : d a b = 0 := by
    dsimp [d]
    rw [hfg a ha, hfg b hb]
    simpa only [ZMod.neg_eq_self_mod_two] using
      add_neg_cancel (tournamentBit T (g a) (g b))
  have hmain : pairSum T f + pairSum T g =
      ∑ a : Fin n, ∑ b : Fin n, if a < b then d a b else 0 := by
    rw [pairSum_eq_sum, pairSum_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : a < b <;> simp [h, d]
  rw [hmain]
  have hrow (a : Fin n) (ha : a ≠ j) :
      (∑ b : Fin n, if a < b then d a b else 0) =
        if a < j then d a j else 0 := by
    apply Finset.sum_eq_single j
    · intro b hb hbj
      rw [hz a b ha hbj]
      split <;> rfl
    · simp
  rw [← Finset.add_sum_erase Finset.univ (fun a : Fin n =>
    ∑ b : Fin n, if a < b then d a b else 0) (Finset.mem_univ j)]
  have hrj : (∑ b : Fin n, if j < b then d j b else 0) =
      ∑ b ∈ Finset.univ.erase j, if j < b then d j b else 0 := by
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro b hb hbj
    have : b = j := by simpa using hbj
    subst b
    simp
  rw [hrj]
  calc
    _ = (∑ i ∈ Finset.univ.erase j, if j < i then d j i else 0) +
        ∑ i ∈ Finset.univ.erase j, if i < j then d i j else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i (Finset.mem_erase.mp hi).1
    _ = ∑ i ∈ Finset.univ.erase j, d j i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hij := (Finset.mem_erase.mp hi).1
      rcases lt_or_gt_of_ne hij with h | h
      · simp [h, not_lt_of_ge h.le, hd i j]
      · simp [h, not_lt_of_ge h.le]
    _ = _ := rfl

private def unitParity (x : ℤˣ) : ZMod 2 := if x = 1 then 0 else 1

private theorem unitParity_mul (x y : ℤˣ) :
    unitParity (x * y) = unitParity x + unitParity y := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy <;>
    simp [unitParity, hx, hy, Units.ext_iff]
  all_goals decide +kernel

private theorem unitParity_prod {α : Type*} (s : Finset α) (f : α → ℤˣ) :
    unitParity (∏ x ∈ s, f x) = ∑ x ∈ s, unitParity (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitParity]
  | @insert a s ha ih => simp [ha, unitParity_mul, ih]

/-- Reindexing pair sums contributes precisely the inversion parity. -/
private theorem pairSum_perm {n : ℕ} {V : Type u} (T : Hyper 2 V)
    (f : Fin n ↪ V) (σ : Equiv.Perm (Fin n)) :
    pairSum T (σ.toEmbedding.trans f) =
      pairSum T f + unitParity (Equiv.Perm.signAux σ) := by
  classical
  let ps := Equiv.Perm.finPairsLT n
  let raw (p : Σ _ : Fin n, Fin n) := tournamentBit T (f p.2) (f p.1)
  have hterm (p : Σ _ : Fin n, Fin n) (hp : p ∈ ps) :
      tournamentBit T (f (σ p.2)) (f (σ p.1)) =
        raw (Equiv.Perm.signBijAux σ p) +
          unitParity (if σ p.1 ≤ σ p.2 then -1 else 1) := by
    have hne : f (σ p.1) ≠ f (σ p.2) := by
      intro he
      have he' := σ.injective (f.injective he)
      exact (Equiv.Perm.mem_finPairsLT.mp hp).ne he'.symm
    by_cases h : σ p.2 < σ p.1
    · simp [Equiv.Perm.signBijAux, h, not_le.mpr h, raw, unitParity]
    · have hle := le_of_not_gt h
      simp only [Equiv.Perm.signBijAux, h, dite_false, raw, hle, ite_true,
        unitParity, show (-1 : ℤˣ) ≠ 1 by decide, ite_false]
      exact tournamentBit_reverse T hne
  have hsum : (∑ p ∈ ps, raw (Equiv.Perm.signBijAux σ p)) = ∑ p ∈ ps, raw p := by
    exact Finset.sum_nbij (Equiv.Perm.signBijAux σ)
      Equiv.Perm.signBijAux_mem Equiv.Perm.signBijAux_injOn
      Equiv.Perm.signBijAux_surj (fun _ _ => rfl)
  calc
    pairSum T (σ.toEmbedding.trans f) =
        ∑ p ∈ ps, (raw (Equiv.Perm.signBijAux σ p) +
          unitParity (if σ p.1 ≤ σ p.2 then -1 else 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ = pairSum T f + unitParity (Equiv.Perm.signAux σ) := by
      rw [Finset.sum_add_distrib, hsum]
      congr 1
      exact (unitParity_prod ps _).symm

theorem pairSum_swap {n : ℕ} {V : Type u} (T : Hyper 2 V)
    (f : Fin n ↪ V) (i j : Fin n) (hij : i ≠ j) :
    pairSum T ((Equiv.swap i j).toEmbedding.trans f) = pairSum T f + 1 := by
  rw [pairSum_perm, Equiv.Perm.signAux_swap hij]
  rfl

/-- Sullivan's sum-induced hypertournament, on its original vertex set. -/
noncomputable def sumInduced {V : Type u} (T : Hyper 2 V) (n : ℕ) : Hyper n V where
  orient f := boolOf (pairSum T f)
  swap_flip f i j hij := by
    rw [pairSum_swap T f i j hij, boolOf_add_one]

@[simp] theorem sumInduced_orient {n : ℕ} {V : Type u} (T : Hyper 2 V)
    (f : Fin n ↪ V) : bit ((sumInduced T n).orient f) = pairSum T f :=
  bit_boolOf _

/-- In arity three the defining sum has its familiar triangle form. -/
theorem pairSum_three {V : Type u} (T : Hyper 2 V) (f : Fin 3 ↪ V) :
    pairSum T f = tournamentBit T (f 0) (f 1) +
      tournamentBit T (f 0) (f 2) + tournamentBit T (f 1) (f 2) := by
  have hp : Equiv.Perm.finPairsLT 3 =
      {(⟨1, 0⟩ : Σ _ : Fin 3, Fin 3), ⟨2, 0⟩, ⟨2, 1⟩} := by decide +kernel
  simp [pairSum, hp, add_assoc]

theorem pairSum_two {V : Type u} (T : Hyper 2 V) (f : Fin 2 ↪ V) :
    pairSum T f = tournamentBit T (f 0) (f 1) := by
  have hp : Equiv.Perm.finPairsLT 2 = {(⟨1, 0⟩ : Σ _ : Fin 2, Fin 2)} := by decide +kernel
  simp [pairSum, hp]

/-- Tournament embeddings induce embeddings in every higher arity. -/
theorem sumInduced_preserves {n : ℕ} {V : Type u} {W : Type v}
    (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W) (he : Preserves T U e) :
    Preserves (sumInduced T n) (sumInduced U n) e := by
  intro f
  apply bit_injective
  rw [sumInduced_orient, sumInduced_orient]
  apply Finset.sum_congr rfl
  intro p hp
  exact tournamentBit_preserves T U e he (f p.2) (f p.1)

end Hypertournaments.Antichain
