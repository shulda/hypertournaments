import Hypertournaments.Independent.Statements
import Hypertournaments.EvenPotential
import Mathlib.Order.RelClasses

/-!
# Carrier-preserving translations of the independent statement language

The independently supplied definitions are retained in `Statements`. This
module identifies their total ZMod orientations with the project's intrinsic
Boolean orientations on injective tuples, without changing the carrier.
-/

namespace IndependentHypertournaments.Bridge

universe u v

open Hypertournaments

noncomputable def toHyper {n : ℕ} {V : Type u}
    (A : Hypertournament n V) : Hyper n V where
  orient t := p3ZMod2ToBool (A.orientation t)
  swap_flip t i j hij := by
    apply p1BitToZMod_injective
    rw [p3BitToZMod_roundtrip, p1BitToZMod_not, p3BitToZMod_roundtrip]
    exact A.alternating t i j t.injective hij

noncomputable def ofHyper {n : ℕ} {V : Type u}
    (A : Hyper n V) : Hypertournament n V := by
  classical
  refine ⟨fun t => if h : Function.Injective t then p1BitToZMod (A.orient ⟨t, h⟩) else 0,
    ?_, ?_⟩
  · intro t ht
    simp only [dite_eq_right ht]
  · intro t i j ht hij
    have hs : Function.Injective (fun k => t ((Equiv.swap i j) k)) :=
      ht.comp (Equiv.swap i j).injective
    simp only [dite_eq_left ht, dite_eq_left hs]
    exact (congrArg p1BitToZMod (A.swap_flip ⟨t, ht⟩ i j hij)).trans
      (p1BitToZMod_not _)

@[simp] theorem bit_toHyper {n : ℕ} {V : Type u}
    (A : Hypertournament n V) (t : Fin n ↪ V) :
    p1BitToZMod ((toHyper A).orient t) = A.orientation t :=
  p3BitToZMod_roundtrip _

@[simp] theorem ofHyper_orientation {n : ℕ} {V : Type u}
    (A : Hyper n V) (t : Fin n ↪ V) :
    (ofHyper A).orientation t = p1BitToZMod (A.orient t) := by
  classical
  simp only [ofHyper, dite_eq_left t.injective]
  apply congrArg (fun f : Fin n ↪ V => p1BitToZMod (A.orient f))
  ext i
  rfl

theorem hypertournament_ext {n : ℕ} {V : Type u} {A B : Hypertournament n V}
    (h : A.orientation = B.orientation) : A = B := by
  cases A
  cases B
  cases h
  rfl

@[simp] theorem toHyper_ofHyper {n : ℕ} {V : Type u} (A : Hyper n V) :
    toHyper (ofHyper A) = A := by
  apply Hyper.ext
  intro t
  apply p1BitToZMod_injective
  rw [bit_toHyper, ofHyper_orientation]

@[simp] theorem ofHyper_toHyper {n : ℕ} {V : Type u} (A : Hypertournament n V) :
    ofHyper (toHyper A) = A := by
  classical
  apply hypertournament_ext
  funext t
  by_cases ht : Function.Injective t
  · exact (ofHyper_orientation (toHyper A) ⟨t, ht⟩).trans (bit_toHyper A ⟨t, ht⟩)
  · exact ((ofHyper (toHyper A)).degenerate t ht).trans (A.degenerate t ht).symm

theorem embeds_iff_preserves {n : ℕ} {V : Type u} {W : Type v}
    (A : Hypertournament n V) (B : Hypertournament n W) (e : V ↪ W) :
    Embeds A B e ↔ Preserves (toHyper A) (toHyper B) e := by
  constructor
  · intro h t
    apply p1BitToZMod_injective
    rw [bit_toHyper, bit_toHyper]
    exact h.2 t
  · intro h
    refine ⟨e.injective, ?_⟩
    intro t
    by_cases ht : Function.Injective t
    · exact (bit_toHyper B ((⟨t, ht⟩ : Fin n ↪ V).trans e)).symm.trans
        ((congrArg p1BitToZMod (h ⟨t, ht⟩)).trans (bit_toHyper A ⟨t, ht⟩))
    · have he : ¬ Function.Injective (fun i => e (t i)) := by
        intro he
        exact ht (fun i j hij => he (congrArg e hij))
      rw [A.degenerate t ht, B.degenerate _ he]

theorem tupleCoboundary_toHyper {n : ℕ} {V : Type u}
    (A : Hypertournament n V) (t : Fin (n + 1) ↪ V) :
    tupleCoboundary (fun f => p1BitToZMod ((toHyper A).orient f)) t =
      IndependentHypertournaments.coboundary A.orientation t := by
  apply Finset.sum_congr rfl
  intro i _
  exact bit_toHyper A (facet t i)

theorem isEven_iff {n : ℕ} {V : Type u} (A : Hypertournament n V) :
    IsEven A ↔ (toHyper A).IsEven := by
  constructor
  · intro h t
    exact (tupleCoboundary_toHyper A t).trans (h t t.injective)
  · intro h t ht
    exact (tupleCoboundary_toHyper A ⟨t, ht⟩).symm.trans (h ⟨t, ht⟩)

theorem isPotential_iff {r : ℕ} {V : Type u}
    (A : Hypertournament (r + 1) V) (φ : Hypertournament r V) :
    (∀ t, Function.Injective t →
      A.orientation t = IndependentHypertournaments.coboundary φ.orientation t) ↔
      IsPotential (toHyper A) (toHyper φ) := by
  constructor
  · intro h t
    exact (tupleCoboundary_toHyper φ t).trans ((h t t.injective).symm.trans
      (bit_toHyper A t).symm)
  · intro h t ht
    exact (bit_toHyper A ⟨t, ht⟩).symm.trans
      ((h ⟨t, ht⟩).symm.trans (tupleCoboundary_toHyper φ ⟨t, ht⟩))

@[instance_reducible] noncomputable def toLinearOrder {V : Type u}
    (o : LinearOrderData V) : LinearOrder V := by
  classical
  letI : IsStrictTotalOrder V o.lt := {
    irrefl := o.irrefl
    trans := o.trans
    trichotomous := by
      intro a b hab hba
      by_contra hne
      rcases o.total a b hne with h | h
      · exact hab h
      · exact hba h }
  exact linearOrderOfSTO o.lt

def ofLinearOrder {V : Type u} (o : LinearOrder V) : LinearOrderData V where
  lt := @LT.lt V o.toLT
  irrefl := by
    let := o
    exact lt_irrefl
  trans := by
    let := o
    exact fun _ _ _ => lt_trans
  total := by
    let := o
    exact fun _ _ => lt_or_gt_of_ne

@[simp] theorem toLinearOrder_lt {V : Type u} (o : LinearOrderData V) (a b : V) :
    @LT.lt V (toLinearOrder o).toLT a b ↔ o.lt a b := Iff.rfl

@[simp] theorem ofLinearOrder_lt {V : Type u} (o : LinearOrder V) (a b : V) :
    (ofLinearOrder o).lt a b ↔ @LT.lt V o.toLT a b := Iff.rfl

end IndependentHypertournaments.Bridge
