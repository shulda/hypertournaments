import Hypertournaments.CyclicRelation
import Hypertournaments.CircularCut
import Mathlib.Tactic.Order

/-!
# The central ternary local type is exactly a circular order

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the cyclic-order case of the small-arity classification. Both directions
use actual injective tuples and the shared minority-count local index.
-/

universe u

namespace Hypertournaments

private theorem circular_packet_count {V : Type u} [LinearOrder V]
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x0 x1 x2 x3 : Bool)
    (h0 : x0 = false ↔ (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b))
    (h1 : x1 = false ↔ b < c) (h2 : x2 = false ↔ a < c)
    (h3 : x3 = false ↔ a < b) :
    min (Finset.univ.filter (fun i : Fin 4 =>
        (![x0, !x1, x2, !x3] : Fin 4 → Bool) i = true)).card
      (4 - (Finset.univ.filter (fun i : Fin 4 =>
        (![x0, !x1, x2, !x3] : Fin 4 → Bool) i = true)).card) = 2 := by
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hbc with hbc | hcb <;>
    rcases lt_or_gt_of_ne hac with hac | hca
  all_goals
    first
    | solve | order
    | cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;>
        (simp_all [lt_asymm]; all_goals decide)

/-- Every four-point packet of an actual circular order has precisely the central type. -/
theorem Hyper.ofCircularOrder_localIndex {V : Type u} [CircularOrder V]
    (f : Fin 4 ↪ V) : localIndex (Hyper.ofCircularOrder : Hyper 3 V) f = 2 := by
  let p := f 0
  let : LinearOrder V := CircularOrder.cutLinearOrder p
  have hroot (i : Fin 4) (hi : i ≠ 0) : f i ≠ p :=
    f.injective.ne hi
  have hroot_iff (i j : Fin 4) (hi : i ≠ 0) :
      sbtw p (f i) (f j) ↔ f i < f j := by
    rw [CircularOrder.cutLinearOrder_lt_iff]
    simp only [hroot i hi, false_and, false_or]
  have h0 : (Hyper.ofCircularOrder : Hyper 3 V).orient (facet f 0) = false ↔
      (f 1 < f 2 ∧ f 2 < f 3) ∨ (f 2 < f 3 ∧ f 3 < f 1) ∨
        (f 3 < f 1 ∧ f 1 < f 2) :=
    (Hyper.ofCircularOrder_orient_eq_false_iff _).trans
      (CircularOrder.cut_sbtw_iff p (f 1) (f 2) (f 3))
  have h1 : (Hyper.ofCircularOrder : Hyper 3 V).orient (facet f 1) = false ↔
      f 2 < f 3 :=
    (Hyper.ofCircularOrder_orient_eq_false_iff _).trans (hroot_iff 2 3 (by decide))
  have h2 : (Hyper.ofCircularOrder : Hyper 3 V).orient (facet f 2) = false ↔
      f 1 < f 3 :=
    (Hyper.ofCircularOrder_orient_eq_false_iff _).trans (hroot_iff 1 3 (by decide))
  have h3 : (Hyper.ofCircularOrder : Hyper 3 V).orient (facet f 3) = false ↔
      f 1 < f 2 :=
    (Hyper.ofCircularOrder_orient_eq_false_iff _).trans (hroot_iff 1 2 (by decide))
  unfold localIndex
  rw [positiveFacetCount_ternary]
  exact circular_packet_count (f.injective.ne (by decide))
    (f.injective.ne (by decide)) (f.injective.ne (by decide)) _ _ _ _ h0 h1 h2 h3

theorem Hyper.ofCircularOrder_admissible_two {V : Type u} [CircularOrder V] :
    Admissible ({2} : Set ℕ) (Hyper.ofCircularOrder : Hyper 3 V) := by
  intro f
  exact Hyper.ofCircularOrder_localIndex f

/-- Central-only ternary packets and Mathlib circular orders are equivalent,
without a finiteness or nonemptiness assumption on the carrier. -/
theorem Hyper.admissible_two_iff_isCyclicOrder {V : Type u} (A : Hyper 3 V) :
    Admissible ({2} : Set ℕ) A ↔ A.IsCyclicOrder := by
  constructor
  · intro hA
    exact ⟨A.cyclicOrder hA, fun t => (A.cyclicOrder_sbtw_iff hA t).symm⟩
  · intro hA
    rcases (A.isCyclicOrder_iff_exists_circular).mp hA with ⟨order, rfl⟩
    let := order
    exact Hyper.ofCircularOrder_admissible_two

/-- A circular order containing four different vertices realizes exactly the
palette `{2}`, so admissibility in any palette is exactly central membership. -/
theorem Hyper.admissible_ofCircularOrder_iff {V : Type u} [CircularOrder V]
    (hfour : Nonempty (Fin 4 ↪ V)) (S : Set ℕ) :
    Admissible S (Hyper.ofCircularOrder : Hyper 3 V) ↔ 2 ∈ S := by
  constructor
  · intro h
    obtain ⟨f⟩ := hfour
    simpa only [Hyper.ofCircularOrder_localIndex] using h f
  · intro h f
    simpa only [Hyper.ofCircularOrder_localIndex] using h

theorem Hyper.ofCircularOrder_localIndex_range {V : Type u} [CircularOrder V]
    (hfour : Nonempty (Fin 4 ↪ V)) :
    Set.range (localIndex (Hyper.ofCircularOrder : Hyper 3 V)) = {2} := by
  ext d
  constructor
  · rintro ⟨f, rfl⟩
    exact Hyper.ofCircularOrder_localIndex f
  · intro hd
    obtain ⟨f⟩ := hfour
    exact ⟨f, (Hyper.ofCircularOrder_localIndex f).trans hd.symm⟩

end Hypertournaments
