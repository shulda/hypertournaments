import Hypertournaments.CircularHyper
import Mathlib.Order.RelClasses

/-!
# Cutting a circular order at a least root

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the cyclic-order cases. The full carrier is retained, with the chosen
root least, and circularizing the resulting order recovers every triple.
-/

universe u v

namespace CircularOrder

variable {V : Type u} [CircularOrder V]

/-- The cut order starts at the root and then follows the circular order. -/
def cutLT (p x y : V) : Prop := (x = p ∧ y ≠ p) ∨ sbtw p x y

theorem cutLT_ne_root_right {p x y : V} (h : cutLT p x y) : y ≠ p := by
  rcases h with h | h
  · exact h.2
  · rintro rfl
    exact sbtw_irrefl_left_right h

instance cutLT_isStrictTotalOrder (p : V) : IsStrictTotalOrder V (cutLT p) where
  irrefl x := by
    rintro (⟨h, hn⟩ | h)
    · exact hn h
    · exact sbtw_irrefl_right h
  trans x y z hxy hyz := by
    rcases hxy with ⟨rfl, hy⟩ | hxy
    · exact Or.inl ⟨rfl, cutLT_ne_root_right hyz⟩
    · rcases hyz with ⟨rfl, hz⟩ | hyz
      · exact (sbtw_irrefl_left_right hxy).elim
      · exact Or.inr (hxy.trans_right hyz)
  trichotomous x y hxy hyx := by
    classical
    by_contra hne
    by_cases hx : x = p
    · exact hxy (Or.inl ⟨hx, fun hy => hne (hx.trans hy.symm)⟩)
    by_cases hy : y = p
    · exact hyx (Or.inl ⟨hy, hx⟩)
    by_cases h : sbtw p x y
    · exact hxy (Or.inr h)
    · exact hyx (Or.inr
        ((Hypertournaments.sbtw_swap_last_iff_not (Ne.symm hx) hne (Ne.symm hy)).mpr h))

/-- The linear order obtained by cutting the circle at a least root. -/
@[instance_reducible] noncomputable def cutLinearOrder (p : V) : LinearOrder V := by
  classical
  exact linearOrderOfSTO (cutLT p)

theorem cutLinearOrder_lt_iff (p x y : V) :
    @LT.lt V (cutLinearOrder p).toLT x y ↔ (x = p ∧ y ≠ p) ∨ sbtw p x y := Iff.rfl

theorem cutLinearOrder_root_le (p x : V) : @LE.le V (cutLinearOrder p).toLE p x := by
  change p = x ∨ cutLT p p x
  by_cases h : x = p
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl ⟨rfl, h⟩)

theorem cutLinearOrder_root_lt_iff (p x : V) :
    @LT.lt V (cutLinearOrder p).toLT p x ↔ x ≠ p := by
  rw [cutLinearOrder_lt_iff]
  simp only [true_and]
  exact or_iff_left sbtw_irrefl_left

theorem sbtw_of_cut_lt_lt (p : V) {a b c : V}
    (hab : @LT.lt V (cutLinearOrder p).toLT a b)
    (hbc : @LT.lt V (cutLinearOrder p).toLT b c) : sbtw a b c := by
  let : LinearOrder V := cutLinearOrder p
  have hbc' : cutLT p b c := hbc
  have hab' : cutLT p a b := hab
  rcases hab' with ⟨rfl, hb⟩ | hab'
  · rcases hbc' with ⟨h, _⟩ | h
    · exact (hb h).elim
    · exact h
  · have hb : b ≠ p := cutLT_ne_root_right (Or.inr hab')
    have hc : c ≠ p := cutLT_ne_root_right hbc'
    have hbc'' : sbtw p b c := hbc'.resolve_left (fun h => hb h.1)
    by_contra h
    have hrev := (Hypertournaments.sbtw_swap_last_iff_not
      (ne_of_lt hab) (ne_of_lt hbc) (ne_of_lt (lt_trans hab hbc))).mpr h
    have hpc : sbtw p c b := hab'.trans_left hrev
    exact hpc.not_btw hbc''.btw.cyclic_left

/-- Circularizing the cut linear order recovers the original strict relation. -/
theorem cut_sbtw_iff (p a b c : V) :
    sbtw a b c ↔
      (@LT.lt V (cutLinearOrder p).toLT a b ∧ @LT.lt V (cutLinearOrder p).toLT b c) ∨
      (@LT.lt V (cutLinearOrder p).toLT b c ∧ @LT.lt V (cutLinearOrder p).toLT c a) ∨
      (@LT.lt V (cutLinearOrder p).toLT c a ∧ @LT.lt V (cutLinearOrder p).toLT a b) := by
  let : LinearOrder V := cutLinearOrder p
  constructor
  · intro h
    have hab : a ≠ b := by rintro rfl; exact sbtw_irrefl_left h
    have hbc : b ≠ c := by rintro rfl; exact sbtw_irrefl_right h
    have hac : a ≠ c := by rintro rfl; exact sbtw_irrefl_left_right h
    rcases lt_or_gt_of_ne hab with hab | hba
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact Or.inl ⟨hab, hbc⟩
      · rcases lt_or_gt_of_ne hac with hac | hca
        · exact (h.not_btw (sbtw_of_cut_lt_lt p hac hcb).btw.cyclic_left).elim
        · exact Or.inr (Or.inr ⟨hca, hab⟩)
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact (h.not_btw (sbtw_of_cut_lt_lt p hba hac).btw.cyclic_right).elim
      · rcases lt_or_gt_of_ne hbc with hbc | hcb
        · exact Or.inr (Or.inl ⟨hbc, hca⟩)
        · exact (h.not_btw (sbtw_of_cut_lt_lt p hcb hba).btw).elim
  · rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩)
    · exact sbtw_of_cut_lt_lt p hab hbc
    · exact (sbtw_of_cut_lt_lt p hbc hca).cyclic_right
    · exact (sbtw_of_cut_lt_lt p hca hab).cyclic_left

/-- An injection preserving the circular relation and the cut root is increasing. -/
theorem cutLinearOrder_strictMono {W : Type v} [CircularOrder W]
    (e : V ↪ W) (p : V) (q : W) (hp : e p = q)
    (he : ∀ a b c : V, a ≠ b → b ≠ c → a ≠ c →
      (sbtw a b c ↔ sbtw (e a) (e b) (e c))) :
    @StrictMono V W (cutLinearOrder p).toPreorder (cutLinearOrder q).toPreorder e := by
  intro x y hxy
  change cutLT q (e x) (e y)
  rcases hxy with ⟨rfl, hy⟩ | hxy
  · exact Or.inl ⟨hp, fun h => hy (e.injective (h.trans hp.symm))⟩
  · apply Or.inr
    have hpx : p ≠ x := by rintro rfl; exact sbtw_irrefl_left hxy
    have hxy' : x ≠ y := by rintro rfl; exact sbtw_irrefl_right hxy
    have hpy : p ≠ y := by rintro rfl; exact sbtw_irrefl_left_right hxy
    simpa only [hp] using (he p x y hpx hxy' hpy).mp hxy

end CircularOrder
