import Hypertournaments.Basic
import Mathlib.Order.Circular
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.FinCases

/-!
# Circular orders as intrinsic ternary hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the finite cyclic-order discussion following `cor:even-no-eppa`.
The positive circular relation is represented by Boolean orientation false.
-/

universe u v

namespace Hypertournaments

private theorem bool_eq_of_false_iff (a b : Bool) (h : a = false ↔ b = false) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem hyper_eq_of_orient_eq {n : ℕ} {V : Type u} {A B : Hyper n V}
    (h : A.orient = B.orient) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem sbtw_iff_btw_of_pairwise_ne {V : Type u} [CircularOrder V]
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw a b c ↔ btw a b c := by
  refine ⟨btw_of_sbtw, fun h => sbtw_of_btw_not_btw h ?_⟩
  intro h'
  rcases btw_antisymm h h' with h | h | h
  · exact hab h
  · exact hbc h
  · exact hac h.symm

theorem sbtw_swap_last_iff_not {V : Type u} [CircularOrder V]
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw a c b ↔ ¬ sbtw a b c := by
  constructor
  · intro h h'
    exact h.not_btw h'.btw.cyclic_left
  · intro h
    have hn : ¬ btw a b c := fun h' =>
      h ((sbtw_iff_btw_of_pairwise_ne hab hbc hac).mpr h')
    have hb := (btw_total a b c).resolve_left hn
    exact (sbtw_iff_btw_of_pairwise_ne hac hbc.symm hab).mpr hb.cyclic_right

theorem sbtw_swap_first_iff_not {V : Type u} [CircularOrder V]
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw b a c ↔ ¬ sbtw a b c := by
  constructor
  · intro h h'
    exact (sbtw_swap_last_iff_not hab hbc hac).mp h.cyclic_left h'
  · intro h
    exact ((sbtw_swap_last_iff_not hab hbc hac).mpr h).cyclic_right

theorem sbtw_swap_outer_iff_not {V : Type u} [CircularOrder V]
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw c b a ↔ ¬ sbtw a b c := by
  constructor
  · intro h h'
    exact h.not_btw h'.btw
  · intro h
    exact ((sbtw_swap_last_iff_not hab hbc hac).mpr h).cyclic_left

/-- The intrinsic orientation of a circular order; false is the clockwise relation. -/
noncomputable def Hyper.ofCircularOrder {V : Type u} [CircularOrder V] : Hyper 3 V where
  orient t := by classical exact !(decide (sbtw (t 0) (t 1) (t 2)))
  swap_flip := by
    classical
    intro t i j hij
    have h01 : t 0 ≠ t 1 := t.injective.ne (by decide)
    have h12 : t 1 ≠ t 2 := t.injective.ne (by decide)
    have h02 : t 0 ≠ t 2 := t.injective.ne (by decide)
    fin_cases i <;> fin_cases j <;>
      simp_all [Function.Embedding.trans_apply, Equiv.swap_apply_def,
        sbtw_swap_first_iff_not h01 h12 h02,
        sbtw_swap_last_iff_not h01 h12 h02,
        sbtw_swap_outer_iff_not h01 h12 h02]

@[simp] theorem Hyper.ofCircularOrder_orient_eq_false_iff {V : Type u}
    [CircularOrder V] (t : Fin 3 ↪ V) :
    (Hyper.ofCircularOrder : Hyper 3 V).orient t = false ↔ sbtw (t 0) (t 1) (t 2) := by
  classical
  simp [Hyper.ofCircularOrder]

/-- An explicit circular order inducing the given intrinsic orientation. -/
def Hyper.CircularCompatible {V : Type u} (A : Hyper 3 V) (order : CircularOrder V) : Prop :=
  ∀ t : Fin 3 ↪ V, A.orient t = false ↔ @sbtw V order.toSBtw (t 0) (t 1) (t 2)

/-- Being a cyclic order is intrinsic; the circular presentation is an existential witness. -/
def Hyper.IsCyclicOrder {V : Type u} (A : Hyper 3 V) : Prop :=
  ∃ order : CircularOrder V, A.CircularCompatible order

theorem Hyper.ofCircularOrder_circularCompatible {V : Type u} (order : CircularOrder V) :
    (@Hyper.ofCircularOrder V order).CircularCompatible order := by
  let := order
  exact Hyper.ofCircularOrder_orient_eq_false_iff

theorem Hyper.ofCircularOrder_isCyclicOrder {V : Type u} [order : CircularOrder V] :
    (Hyper.ofCircularOrder : Hyper 3 V).IsCyclicOrder :=
  ⟨order, Hyper.ofCircularOrder_circularCompatible order⟩

theorem Hyper.circularCompatible_iff_eq {V : Type u} (A : Hyper 3 V)
    (order : CircularOrder V) :
    A.CircularCompatible order ↔ A = @Hyper.ofCircularOrder V order := by
  let := order
  constructor
  · intro h
    have hfun : A.orient = (@Hyper.ofCircularOrder V order).orient := by
      funext t
      have hh : A.orient t = false ↔ (@Hyper.ofCircularOrder V order).orient t = false :=
        (h t).trans (Hyper.ofCircularOrder_orient_eq_false_iff t).symm
      exact bool_eq_of_false_iff _ _ hh
    exact hyper_eq_of_orient_eq hfun
  · rintro rfl
    exact Hyper.ofCircularOrder_circularCompatible order

theorem Hyper.isCyclicOrder_iff_exists_circular {V : Type u} (A : Hyper 3 V) :
    A.IsCyclicOrder ↔ ∃ order : CircularOrder V, A = @Hyper.ofCircularOrder V order := by
  simp only [Hyper.IsCyclicOrder, Hyper.circularCompatible_iff_eq]

/-- The tuple formed by three pairwise different vertices. -/
def circularTriple {V : Type u} (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : Fin 3 ↪ V :=
  Fin.Embedding.cons (Function.Embedding.embFinTwo hbc) (by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hab hi.symm
    · exact hac hi.symm)

@[simp] theorem circularTriple_zero {V : Type u} (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : circularTriple a b c hab hbc hac 0 = a := rfl

@[simp] theorem circularTriple_one {V : Type u} (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : circularTriple a b c hab hbc hac 1 = b := rfl

@[simp] theorem circularTriple_two {V : Type u} (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : circularTriple a b c hab hbc hac 2 = c := rfl

/-- Preserving intrinsic orientations is exactly preserving the strict circular relation. -/
theorem preserves_iff_sbtw {V : Type u} {W : Type v}
    {A : Hyper 3 V} {B : Hyper 3 W} (orderV : CircularOrder V) (orderW : CircularOrder W)
    (hA : A.CircularCompatible orderV) (hB : B.CircularCompatible orderW) (e : V ↪ W) :
    Preserves A B e ↔ ∀ a b c : V, a ≠ b → b ≠ c → a ≠ c →
      (@sbtw V orderV.toSBtw a b c ↔ @sbtw W orderW.toSBtw (e a) (e b) (e c)) := by
  constructor
  · intro he a b c hab hbc hac
    let t := circularTriple a b c hab hbc hac
    have h := (hA t).symm.trans ((he t) ▸ hB (t.trans e))
    exact h
  · intro he t
    have h := (hB (t.trans e)).trans
      ((he (t 0) (t 1) (t 2) (t.injective.ne (by decide))
        (t.injective.ne (by decide)) (t.injective.ne (by decide))).symm.trans (hA t).symm)
    cases ha : A.orient t <;> cases hb : B.orient (t.trans e) <;> simp_all

end Hypertournaments
