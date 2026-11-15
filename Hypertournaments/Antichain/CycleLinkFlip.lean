import Hypertournaments.Antichain.CycleTournament
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-!
# A nonconstant cycle link

A small nonempty set cannot have the same tournament link value at every
vertex of its complement. We use the generous size bound needed by the
antichain, rather than optimizing Sullivan's bound.
-/

namespace Hypertournaments.Antichain

private theorem exists_three_gap (N : ℕ) (B : Finset ℕ)
    (hN : 3 * B.card + 2 < N) :
    ∃ t, t + 2 < N ∧ t ∉ B ∧ t + 1 ∉ B ∧ t + 2 ∉ B := by
  classical
  let blocked := B ∪ B.image (fun x => x - 1) ∪ B.image (fun x => x - 2)
  have hcard : blocked.card ≤ 3 * B.card := by
    calc
      blocked.card ≤ (B ∪ B.image (fun x => x - 1)).card +
          (B.image (fun x => x - 2)).card := Finset.card_union_le _ _
      _ ≤ (B.card + (B.image (fun x => x - 1)).card) +
          (B.image (fun x => x - 2)).card := Nat.add_le_add_right
            (Finset.card_union_le _ _) _
      _ ≤ (B.card + B.card) + B.card := by
        exact Nat.add_le_add (Nat.add_le_add_left (Finset.card_image_le) _)
          (Finset.card_image_le)
      _ = 3 * B.card := by omega
  have hnot : ¬ Finset.range (N - 2) ⊆ blocked := by
    intro h
    have := Finset.card_le_card h
    simp only [Finset.card_range] at this
    omega
  obtain ⟨t, ht, htb⟩ := Finset.not_subset.mp hnot
  have htN := Finset.mem_range.mp ht
  refine ⟨t, by omega, ?_, ?_, ?_⟩
  · intro h
    exact htb (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  · intro h
    apply htb
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨t + 1, h, by omega⟩
  · intro h
    apply htb
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨t + 2, h, by omega⟩

private theorem exists_natural_boundary (N : ℕ) (B : Finset ℕ)
    (hB : B.Nonempty) (hBN : ∀ b ∈ B, b < N)
    (hN : 3 * B.card + 2 < N) :
    ∃ a c r, a < N ∧ c < N ∧ r ∈ B ∧ a ∉ B ∧ c ∉ B ∧
      (∀ b ∈ B, (b < a ↔ b < c)) ∧
      (∀ b ∈ B,
        (a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ b + 1 = N) ∨
          (b = 0 ∧ a + 1 = N)) ↔ b = r) ∧
      (∀ b ∈ B,
        ¬ (c + 1 = b ∨ b + 1 = c ∨ (c = 0 ∧ b + 1 = N) ∨
          (b = 0 ∧ c + 1 = N))) := by
  classical
  obtain ⟨t, htN, ht0, ht1, ht2⟩ := exists_three_gap N B hN
  by_cases hright : (B.filter (fun b => t + 2 < b)).Nonempty
  · let R := B.filter (fun b => t + 2 < b)
    let r := R.min' hright
    have hrmem : r ∈ B := (Finset.mem_filter.mp (Finset.min'_mem R hright)).1
    have hr : t + 2 < r := (Finset.mem_filter.mp (Finset.min'_mem R hright)).2
    have hrN := hBN r hrmem
    have hgap (x : ℕ) (hxt : t ≤ x) (hxr : x < r) : x ∉ B := by
      intro hx
      by_cases htx : t + 2 < x
      · have hle : r ≤ x := Finset.min'_le R x (Finset.mem_filter.mpr ⟨hx, htx⟩)
        omega
      · have he : x = t ∨ x = t + 1 ∨ x = t + 2 := by omega
        rcases he with rfl | rfl | rfl
        · exact ht0 hx
        · exact ht1 hx
        · exact ht2 hx
    have ha := hgap (r - 1) (by omega) (by omega)
    have hc := hgap (r - 2) (by omega) (by omega)
    have hd := hgap (r - 3) (by omega) (by omega)
    refine ⟨r - 1, r - 2, r, by omega, by omega, hrmem, ha, hc, ?_, ?_, ?_⟩
    · intro b hb
      have hba : b ≠ r - 1 := fun h => ha (h ▸ hb)
      have hbc : b ≠ r - 2 := fun h => hc (h ▸ hb)
      omega
    · intro b hb
      have hbN := hBN b hb
      have hbc : b ≠ r - 2 := fun h => hc (h ▸ hb)
      omega
    · intro b hb
      have hbN := hBN b hb
      have hba : b ≠ r - 1 := fun h => ha (h ▸ hb)
      have hbd : b ≠ r - 3 := fun h => hd (h ▸ hb)
      omega
  · let r := B.max' hB
    have hrmem : r ∈ B := Finset.max'_mem B hB
    have hrN := hBN r hrmem
    have hr : r < t := by
      have hnot : ¬ t + 2 < r := by
        intro h
        exact hright ⟨r, Finset.mem_filter.mpr ⟨hrmem, h⟩⟩
      have h0 : r ≠ t := fun h => ht0 (h ▸ hrmem)
      have h1 : r ≠ t + 1 := fun h => ht1 (h ▸ hrmem)
      have h2 : r ≠ t + 2 := fun h => ht2 (h ▸ hrmem)
      omega
    have hmax (b : ℕ) (hb : b ∈ B) : b ≤ r := Finset.le_max' B b hb
    have ha : r + 1 ∉ B := by intro h; have := hmax _ h; omega
    have hc : r + 2 ∉ B := by intro h; have := hmax _ h; omega
    refine ⟨r + 1, r + 2, r, by omega, by omega, hrmem, ha, hc, ?_, ?_, ?_⟩
    · intro b hb
      have := hmax b hb
      omega
    · intro b hb
      have := hmax b hb
      omega
    · intro b hb
      have := hmax b hb
      omega

/-- Two vertices outside a small nonempty set have opposite link sums:
their pointwise direction differences are supported at exactly one vertex
of that set. This statement does not use an auxiliary order. -/
theorem exists_cycle_link_flip {N : ℕ} (B : Finset (Fin N))
    (hB : B.Nonempty) (hN : 3 * B.card + 2 < N) :
    ∃ a c r : Fin N, a ∉ B ∧ c ∉ B ∧ r ∈ B ∧
      ∀ b ∈ B,
        (cycleTournamentBit a b ^^ cycleTournamentBit c b) = decide (b = r) := by
  classical
  let S := B.image Fin.val
  have hScard : S.card = B.card := Finset.card_image_of_injective _ Fin.val_injective
  have hS : S.Nonempty := hB.image _
  have hSN (b : ℕ) (hb : b ∈ S) : b < N := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    exact b.isLt
  obtain ⟨a, c, r, haN, hcN, hr, ha, hc, hcmp, hadj, hnadj⟩ :=
    exists_natural_boundary N S hS hSN (by omega)
  let af : Fin N := ⟨a, haN⟩
  let cf : Fin N := ⟨c, hcN⟩
  let rf : Fin N := ⟨r, hSN r hr⟩
  have hrf : rf ∈ B := by
    obtain ⟨b, hb, hbr⟩ := Finset.mem_image.mp hr
    have he : b = rf := Fin.ext hbr
    exact he ▸ hb
  refine ⟨af, cf, rf, ?_, ?_, hrf, ?_⟩
  · intro h
    exact ha (Finset.mem_image.mpr ⟨af, h, rfl⟩)
  · intro h
    exact hc (Finset.mem_image.mpr ⟨cf, h, rfl⟩)
  · intro b hb
    have hbS : b.val ∈ S := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have hcmp' : b < af ↔ b < cf := hcmp b.val hbS
    have hadj' : cycleAdj af b ↔ b = rf := by
      simpa only [cycleAdj, af, rf, Fin.ext_iff] using hadj b.val hbS
    have hnadj' : ¬ cycleAdj cf b := hnadj b.val hbS
    simp only [cycleTournamentBit, hcmp', hadj', hnadj', decide_false, Bool.xor_false]
    cases decide (b < cf) <;> cases decide (b = rf) <;> rfl

end Hypertournaments.Antichain
