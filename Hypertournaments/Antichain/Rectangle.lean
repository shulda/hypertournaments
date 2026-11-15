import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# Four-set cancellation for symmetric edge labels

If all `k`-element sets have zero total edge label over `ZMod 2`, four
such equations on a common `(k-2)`-element set give a rectangle equation.
Consequently every triangle has the same total edge label.
-/

namespace Hypertournaments.Antichain

open Finset

variable {V : Type*} [LinearOrder V]

/-- Sum each unordered pair once, using the ambient order only to enumerate it. -/
def pairSetSum (d : V → V → ZMod 2) (s : Finset V) : ZMod 2 :=
  ∑ x ∈ s, ∑ y ∈ s, if x < y then d x y else 0

theorem pairSetSum_insert (d : V → V → ZMod 2)
    (hsym : ∀ x y, d x y = d y x) {s : Finset V} {a : V} (ha : a ∉ s) :
    pairSetSum d (insert a s) = pairSetSum d s + ∑ b ∈ s, d a b := by
  classical
  unfold pairSetSum
  rw [sum_insert ha]
  simp_rw [sum_insert ha]
  simp only [lt_self_iff_false, ↓reduceIte, zero_add]
  rw [sum_add_distrib]
  have hcross :
      (∑ b ∈ s, if a < b then d a b else 0) +
        (∑ b ∈ s, if b < a then d b a else 0) = ∑ b ∈ s, d a b := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b hb
    have hab : a ≠ b := fun heq => ha (heq ▸ hb)
    rcases lt_or_gt_of_ne hab with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h, ← hsym a b]
  rw [← hcross]
  ring

theorem pairSetSum_insert_two (d : V → V → ZMod 2)
    (hsym : ∀ x y, d x y = d y x) {s : Finset V} {a b : V}
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b) :
    pairSetSum d (insert a (insert b s)) =
      pairSetSum d s + (∑ x ∈ s, d a x) + (∑ x ∈ s, d b x) + d a b := by
  rw [pairSetSum_insert d hsym (by simp [ha, hab]),
    pairSetSum_insert d hsym hb, sum_insert hb]
  ring

/-- Cancel the four common-support equations. -/
theorem rectangle_of_zero_pairSetSum (d : V → V → ZMod 2)
    (hsym : ∀ x y, d x y = d y x) {k : ℕ} (hk : 2 ≤ k)
    (hzero : ∀ s : Finset V, s.card = k → pairSetSum d s = 0)
    {s : Finset V} (hcard : s.card = k - 2)
    {a b c e : V} (ha : a ∉ s) (hb : b ∉ s) (hc : c ∉ s) (he : e ∉ s)
    (hac : a ≠ c) (hbc : b ≠ c) (hae : a ≠ e) (hbe : b ≠ e) :
    d a c + d b c + d a e + d b e = 0 := by
  have hsz {u v : V} (hu : u ∉ s) (hv : v ∉ s) (huv : u ≠ v) :
      (insert u (insert v s)).card = k := by
    rw [card_insert_of_notMem (by simp [hu, huv]), card_insert_of_notMem hv, hcard]
    omega
  have h₁ := hzero _ (hsz ha hc hac)
  have h₂ := hzero _ (hsz hb hc hbc)
  have h₃ := hzero _ (hsz ha he hae)
  have h₄ := hzero _ (hsz hb he hbe)
  rw [pairSetSum_insert_two d hsym ha hc hac] at h₁
  rw [pairSetSum_insert_two d hsym hb hc hbc] at h₂
  rw [pairSetSum_insert_two d hsym ha he hae] at h₃
  rw [pairSetSum_insert_two d hsym hb he hbe] at h₄
  linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide,
    show (4 : ZMod 2) = 0 by decide])) h₁ + h₂ + h₃ + h₄

/-- There is enough common support for every four-vertex rectangle. -/
theorem all_rectangles_of_zero_pairSetSum [Fintype V]
    (d : V → V → ZMod 2) (hsym : ∀ x y, d x y = d y x)
    {k : ℕ} (hk : 2 ≤ k) (hV : k + 2 ≤ Fintype.card V)
    (hzero : ∀ s : Finset V, s.card = k → pairSetSum d s = 0)
    {a b c e : V} (hac : a ≠ c) (hbc : b ≠ c) (hae : a ≠ e) (hbe : b ≠ e) :
    d a c + d b c + d a e + d b e = 0 := by
  classical
  let T : Finset V := {a, b, c, e}
  have hT : T.card ≤ 4 := by
    dsimp [T]
    have h₁ := card_insert_le a {b, c, e}
    have h₂ := card_insert_le b {c, e}
    have h₃ := card_insert_le c {e}
    simp only [card_singleton] at h₃
    omega
  have hroom : k - 2 ≤ (univ \ T).card := by
    have h := le_card_sdiff T (univ : Finset V)
    simp only [card_univ] at h
    omega
  obtain ⟨s, hs, hscard⟩ := exists_subset_card_eq hroom
  have ha : a ∉ s := by
    intro h
    have := (mem_sdiff.mp (hs h)).2
    exact this (by simp [T])
  have hb : b ∉ s := by
    intro h
    have := (mem_sdiff.mp (hs h)).2
    exact this (by simp [T])
  have hc : c ∉ s := by
    intro h
    have := (mem_sdiff.mp (hs h)).2
    exact this (by simp [T])
  have he : e ∉ s := by
    intro h
    have := (mem_sdiff.mp (hs h)).2
    exact this (by simp [T])
  exact rectangle_of_zero_pairSetSum d hsym hk hzero hscard ha hb hc he hac hbc hae hbe

/-- The symmetric edge total on one triangle. -/
def triangleSum (d : V → V → ZMod 2) (a b c : V) : ZMod 2 :=
  d a b + d a c + d b c

omit [LinearOrder V] in
theorem triangleSum_swap_left (d : V → V → ZMod 2)
    (hsym : ∀ x y, d x y = d y x) (a b c : V) :
    triangleSum d a b c = triangleSum d b a c := by
  unfold triangleSum
  rw [hsym a b]
  ring

omit [LinearOrder V] in
theorem triangleSum_swap_right (d : V → V → ZMod 2)
    (hsym : ∀ x y, d x y = d y x) (a b c : V) :
    triangleSum d a b c = triangleSum d a c b := by
  unfold triangleSum
  rw [hsym b c]
  ring

/-- Two triangles with a common edge have the same total. -/
theorem triangleSum_eq_of_common_pair [Fintype V]
    (d : V → V → ZMod 2) (hsym : ∀ x y, d x y = d y x)
    {k : ℕ} (hk : 2 ≤ k) (hV : k + 2 ≤ Fintype.card V)
    (hzero : ∀ s : Finset V, s.card = k → pairSetSum d s = 0)
    {a b c e : V} (hac : a ≠ c) (hbc : b ≠ c) (hae : a ≠ e) (hbe : b ≠ e) :
    triangleSum d a b c = triangleSum d a b e := by
  have h := all_rectangles_of_zero_pairSetSum d hsym hk hV hzero hac hbc hae hbe
  unfold triangleSum
  linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) h

/-- The four-set identities make the triangle total independent of its vertices. -/
theorem triangleSum_eq_of_distinct [Fintype V]
    (d : V → V → ZMod 2) (hsym : ∀ x y, d x y = d y x)
    {k : ℕ} (hk : 2 ≤ k) (hV : k + 2 ≤ Fintype.card V)
    (hzero : ∀ s : Finset V, s.card = k → pairSetSum d s = 0)
    {a b c x y z : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triangleSum d x y z = triangleSum d a b c := by
  have common {p q r s : V} (hpr : p ≠ r) (hqr : q ≠ r)
      (hps : p ≠ s) (hqs : q ≠ s) :
      triangleSum d p q r = triangleSum d p q s :=
    triangleSum_eq_of_common_pair d hsym hk hV hzero hpr hqr hps hqs
  have hatriangle (u v : V) (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
      triangleSum d a u v = triangleSum d a b c := by
    by_cases hub : u = b
    · subst u
      exact common hav huv hac hbc
    by_cases hvb : v = b
    · subst v
      rw [triangleSum_swap_right d hsym a u b]
      exact common hau (Ne.symm hub) hac hbc
    calc
      triangleSum d a u v = triangleSum d a u b := common hav huv hab hub
      _ = triangleSum d a b u := triangleSum_swap_right d hsym a u b
      _ = triangleSum d a b c := common hau (Ne.symm hub) hac hbc
  by_cases hxa : x = a
  · subst x
    exact hatriangle y z hxy hxz hyz
  by_cases hya : y = a
  · subst y
    rw [triangleSum_swap_left d hsym x a z]
    exact hatriangle x z hxy.symm hyz hxz
  by_cases hza : z = a
  · subst z
    rw [triangleSum_swap_right d hsym x y a, triangleSum_swap_left d hsym x a y]
    exact hatriangle x y hxz.symm hyz.symm hxy
  calc
    triangleSum d x y z =
        triangleSum d a x y + triangleSum d a x z + triangleSum d a y z := by
      unfold triangleSum
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide]
    _ = triangleSum d a b c := by
      rw [hatriangle x y (Ne.symm hxa) (Ne.symm hya) hxy,
        hatriangle x z (Ne.symm hxa) (Ne.symm hza) hxz,
        hatriangle y z (Ne.symm hya) (Ne.symm hza) hyz]
      ring_nf
      simp [show (3 : ZMod 2) = 1 by decide]

/-- A single label describes the totals of all injective triangles. -/
theorem triangleSum_constant [Fintype V]
    (d : V → V → ZMod 2) (hsym : ∀ x y, d x y = d y x)
    {k : ℕ} (hk : 2 ≤ k) (hV : k + 2 ≤ Fintype.card V)
    (hzero : ∀ s : Finset V, s.card = k → pairSetSum d s = 0) :
    ∃ q : ZMod 2, ∀ f : Fin 3 ↪ V,
      triangleSum d (f 0) (f 1) (f 2) = q := by
  classical
  have h3 : Fintype.card (Fin 3) ≤ Fintype.card V := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h3
  refine ⟨triangleSum d (e 0) (e 1) (e 2), ?_⟩
  intro f
  apply triangleSum_eq_of_distinct d hsym hk hV hzero
  all_goals first
    | exact e.injective.ne (by decide)
    | exact f.injective.ne (by decide)

end Hypertournaments.Antichain
