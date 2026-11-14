import Hypertournaments.LocalTypes
import Hypertournaments.CircularHyper
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Circular
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext

/-!
# Circular relations from central ternary packets

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the four-constrained ternary cyclic-order class (proof preparation,
small-arity obligation). The construction works on arbitrary carriers,
including the empty carrier; it uses the four-point packet directly.
-/

universe u

namespace Hypertournaments

/-- The intrinsic strict ternary relation encoded by the negative orientation. -/
def Hyper.cyclicRel {V : Type u} (A : Hyper 3 V) (a b c : V) : Prop :=
  ∃ t : Fin 3 ↪ V, t 0 = a ∧ t 1 = b ∧ t 2 = c ∧ A.orient t = false

theorem Hyper.cyclicRel_iff_orient {V : Type u} (A : Hyper 3 V) (t : Fin 3 ↪ V) :
    A.cyclicRel (t 0) (t 1) (t 2) ↔ A.orient t = false := by
  constructor
  · rintro ⟨s, h0, h1, h2, hs⟩
    have : s = t := by
      ext i
      fin_cases i <;> assumption
    simpa [this] using hs
  · exact fun h => ⟨t, rfl, rfl, rfl, h⟩

theorem Hyper.cyclicRel_distinct {V : Type u} {A : Hyper 3 V} {a b c : V}
    (h : A.cyclicRel a b c) : a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  rcases h with ⟨t, rfl, rfl, rfl, _⟩
  exact ⟨fun h => (by decide : (0 : Fin 3) ≠ 1) (t.injective h),
    fun h => (by decide : (1 : Fin 3) ≠ 2) (t.injective h),
    fun h => (by decide : (2 : Fin 3) ≠ 0) (t.injective h)⟩

private def cycleThree : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

private theorem cycleThree_sign : cycleThree.sign = 1 := by
  simp [cycleThree, Equiv.Perm.sign_mul]

theorem Hyper.cyclicRel_cyclic {V : Type u} {A : Hyper 3 V} {a b c : V}
    (h : A.cyclicRel a b c) : A.cyclicRel b c a := by
  rcases h with ⟨t, h0, h1, h2, ht⟩
  refine ⟨cycleThree.toEmbedding.trans t, ?_, ?_, ?_, ?_⟩
  · change t (cycleThree 0) = b
    rw [show cycleThree 0 = 1 by decide]
    exact h1
  · change t (cycleThree 1) = c
    rw [show cycleThree 1 = 2 by decide]
    exact h2
  · change t (cycleThree 2) = a
    rw [show cycleThree 2 = 0 by decide]
    exact h0
  · rw [A.orient_perm, cycleThree_sign]
    simpa using ht

theorem Hyper.cyclicRel_asymm {V : Type u} {A : Hyper 3 V} {a b c : V}
    (h : A.cyclicRel a b c) : ¬A.cyclicRel c b a := by
  rcases h with ⟨t, h0, h1, h2, ht⟩
  rintro ⟨s, hs0, hs1, hs2, hs⟩
  have he : s = (Equiv.swap (0 : Fin 3) 2).toEmbedding.trans t := by
    ext i
    fin_cases i <;> simp_all [Equiv.swap_apply_def]
  have hh := A.swap_flip t 0 2 (by decide)
  rw [← he, ht, hs] at hh
  contradiction

theorem Hyper.cyclicRel_total {V : Type u} (A : Hyper 3 V) {a b c : V}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    A.cyclicRel a b c ∨ A.cyclicRel c b a := by
  let t := circularTriple a b c hab hbc hca.symm
  cases ht : A.orient t with
  | false => exact Or.inl ⟨t, rfl, rfl, rfl, ht⟩
  | true =>
    refine Or.inr ⟨(Equiv.swap (0 : Fin 3) 2).toEmbedding.trans t,
      ?_, ?_, ?_, ?_⟩
    · change t ((Equiv.swap (0 : Fin 3) 2) _) = _
      rw [show (Equiv.swap (0 : Fin 3) 2) 0 = 2 by decide]
      rfl
    · change t ((Equiv.swap (0 : Fin 3) 2) _) = _
      rw [show (Equiv.swap (0 : Fin 3) 2) 1 = 1 by decide]
      rfl
    · change t ((Equiv.swap (0 : Fin 3) 2) _) = _
      rw [show (Equiv.swap (0 : Fin 3) 2) 2 = 0 by decide]
      rfl
    · rw [A.swap_flip _ _ _ (by decide), ht]
      rfl

theorem positiveFacetCount_ternary {V : Type u} (A : Hyper 3 V)
    (f : Fin 4 ↪ V) :
    positiveFacetCount A f =
      (Finset.univ.filter (fun i : Fin 4 =>
        (![A.orient (facet f 0), !(A.orient (facet f 1)),
          A.orient (facet f 2), !(A.orient (facet f 3))] : Fin 4 → Bool) i = true)).card := by
  have he : normalizedFacet A f =
      (![A.orient (facet f 0), !(A.orient (facet f 1)),
        A.orient (facet f 2), !(A.orient (facet f 3))] : Fin 4 → Bool) := by
    funext i
    fin_cases i <;> simp [normalizedFacet]
  unfold positiveFacetCount
  rw [he]

theorem Hyper.ternary_packet_trans {V : Type u} (A : Hyper 3 V)
    (f : Fin 4 ↪ V) (h : localIndex A f = 2)
    (h0 : A.orient (facet f 0) = false) (h2 : A.orient (facet f 2) = false) :
    A.orient (facet f 1) = false := by
  unfold localIndex at h
  rw [positiveFacetCount_ternary, h0, h2] at h
  have hb : ∀ x y : Bool,
      min (Finset.univ.filter (fun i : Fin 4 =>
          (![false, !x, false, !y] : Fin 4 → Bool) i = true)).card
        (4 - (Finset.univ.filter (fun i : Fin 4 =>
          (![false, !x, false, !y] : Fin 4 → Bool) i = true)).card) = 2 → x = false := by
    decide
  exact hb _ _ h

theorem Hyper.cyclicRel_trans {V : Type u} {A : Hyper 3 V}
    (hA : Admissible ({2} : Set ℕ) A) {a b c d : V}
    (h : A.cyclicRel a b c) (h' : A.cyclicRel b d c) : A.cyclicRel a d c := by
  classical
  obtain ⟨hab, hbc, hca⟩ := Hyper.cyclicRel_distinct h
  obtain ⟨hbd, hdc, hcb⟩ := Hyper.cyclicRel_distinct h'
  have had : a ≠ d := by
    intro he
    subst d
    exact Hyper.cyclicRel_asymm h (Hyper.cyclicRel_cyclic (Hyper.cyclicRel_cyclic h'))
  let f : Fin 4 ↪ V := ⟨![a, b, d, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hf0 : A.orient (facet f 0) = false := by
    apply (A.cyclicRel_iff_orient _).mp
    exact h'
  have hf2 : A.orient (facet f 2) = false := by
    apply (A.cyclicRel_iff_orient _).mp
    exact h
  have hf1 := A.ternary_packet_trans f (hA f) hf0 hf2
  have hh := (A.cyclicRel_iff_orient (facet f 1)).mpr hf1
  exact hh

/-- Every central-only ternary structure carries its intrinsic circular order. -/
@[instance_reducible] def Hyper.cyclicOrder {V : Type u} (A : Hyper 3 V)
    (hA : Admissible ({2} : Set ℕ) A) : CircularOrder V where
  btw a b c := a = b ∨ b = c ∨ c = a ∨ A.cyclicRel a b c
  sbtw := A.cyclicRel
  btw_refl a := Or.inl rfl
  btw_cyclic_left := by
    intro a b c h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Hyper.cyclicRel_cyclic h)))
  sbtw_iff_btw_not_btw := by
    intro a b c
    constructor
    · intro h
      refine ⟨Or.inr (Or.inr (Or.inr h)), ?_⟩
      obtain ⟨hab, hbc, hca⟩ := Hyper.cyclicRel_distinct h
      rintro (hcb | hba | hac | hr)
      · exact hbc hcb.symm
      · exact hab hba.symm
      · exact hca hac.symm
      · exact Hyper.cyclicRel_asymm h hr
    · rintro ⟨h, hn⟩
      rcases h with hab | hbc | hca | h
      · exact False.elim (hn (Or.inr (Or.inl hab.symm)))
      · exact False.elim (hn (Or.inl hbc.symm))
      · exact False.elim (hn (Or.inr (Or.inr (Or.inl hca.symm))))
      · exact h
  sbtw_trans_left := A.cyclicRel_trans hA
  btw_antisymm := by
    intro a b c h hr
    rcases h with hab | hbc | hca | h
    · exact Or.inl hab
    · exact Or.inr (Or.inl hbc)
    · exact Or.inr (Or.inr hca)
    rcases hr with hcb | hba | hac | hr
    · exact Or.inr (Or.inl hcb.symm)
    · exact Or.inl hba.symm
    · exact Or.inr (Or.inr hac.symm)
    · exact False.elim (Hyper.cyclicRel_asymm h hr)
  btw_total := by
    intro a b c
    by_cases hab : a = b
    · exact Or.inl (Or.inl hab)
    by_cases hbc : b = c
    · exact Or.inl (Or.inr (Or.inl hbc))
    by_cases hca : c = a
    · exact Or.inl (Or.inr (Or.inr (Or.inl hca)))
    rcases A.cyclicRel_total hab hbc hca with h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem Hyper.cyclicOrder_sbtw_iff {V : Type u} (A : Hyper 3 V)
    (hA : Admissible ({2} : Set ℕ) A) (t : Fin 3 ↪ V) :
    @sbtw V (A.cyclicOrder hA).toSBtw (t 0) (t 1) (t 2) ↔ A.orient t = false :=
  A.cyclicRel_iff_orient t

end Hypertournaments
