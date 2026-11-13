import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.EvenSuspensionSigns

/-!
# Counting padding vertices when one facet is deleted

Let Q be an (n+3)-set in the even suspension, and let h be its
number of pads. Deleting a single vertex either preserves h or
decreases it by exactly one. We prove the exact combinatorial
claim for the concrete pad projection, not just an abstract count.

It follows immediately that if h is 0 or 1, or h >= 4, then every
(n+2)-facet of Q has a number of pads different from 2, and hence
has positive sign in the suspended sign table.

This discharges the finite-set part of all the even-suspension
non-two-pad / non-three-pad local cases, independent of arity.
-/

namespace Hypertournaments

/-- Removing one specified pad corresponds exactly to erasing its
index from the pad projection. -/
theorem evenPadProjection_erase_pad
    (m k : ℕ) (Q : Finset (Fin (m + k))) (p : Fin m) :
    evenPadProjection m k (Q.erase (evenPadShift m k p)) =
      (evenPadProjection m k Q).erase p := by
  ext x
  simp only [evenPadProjection, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hneq, hmem⟩
    refine ⟨?_, hmem⟩
    intro hx
    exact hneq (congrArg (evenPadShift m k) hx)
  · rintro ⟨hneq, hmem⟩
    refine ⟨?_, hmem⟩
    intro hx
    exact hneq ((evenPadShift m k).injective hx)

/-- Removing a vertex that is not a pad leaves the pad projection
unchanged. -/
theorem evenPadProjection_erase_nonpad
    (m k : ℕ) (Q : Finset (Fin (m + k)))
    (v : Fin (m + k))
    (hnot : v ∉ Set.range (evenPadShift m k)) :
    evenPadProjection m k (Q.erase v) =
      evenPadProjection m k Q := by
  ext x
  have hneq : evenPadShift m k x ≠ v := by
    intro h
    exact hnot ⟨x, h⟩
  simp [evenPadProjection, hneq]

/-- Erasing a vertex can lower the number of pads by at most one;
it can never increase that number. -/
theorem evenPadProjection_erase_card
    (m k : ℕ) (Q : Finset (Fin (m + k)))
    (v : Fin (m + k)) :
    (evenPadProjection m k (Q.erase v)).card =
        (evenPadProjection m k Q).card ∨
      (evenPadProjection m k (Q.erase v)).card + 1 =
        (evenPadProjection m k Q).card := by
  by_cases hp : v ∈ Set.range (evenPadShift m k)
  · obtain ⟨p, hpv⟩ := hp
    subst v
    rw [evenPadProjection_erase_pad]
    by_cases hmem : p ∈ evenPadProjection m k Q
    · right
      exact Finset.card_erase_add_one hmem
    · left
      simp [Finset.erase_eq_self.mpr hmem]
  · left
    rw [evenPadProjection_erase_nonpad m k Q v hp]

/-- No facet can have exactly two pads when the parent packet has
at most one pad, or at least four pads. -/
theorem evenPadProjection_erase_ne_two
    (m k : ℕ) (Q : Finset (Fin (m + k)))
    (hcount : (evenPadProjection m k Q).card ≤ 1 ∨
      4 ≤ (evenPadProjection m k Q).card)
    (v : Fin (m + k)) :
    (evenPadProjection m k (Q.erase v)).card ≠ 2 := by
  have h :=
    evenPadProjection_erase_card m k Q v
  rcases hcount with hlo | hhi <;> rcases h with hh | hh <;> omega

/-- Every facet of a packet whose pad count is 0,1, or >=4
has positive raw orientation in the even suspension sign table. -/
theorem evenSuspensionSignTable_facet_positive
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k)))
    (hcount : (evenPadProjection m k Q).card ≤ 1 ∨
      4 ≤ (evenPadProjection m k Q).card)
    (v : Fin (m + k)) :
    evenSuspensionSignTable m k A (Q.erase v) = true := by
  have hne := evenPadProjection_erase_ne_two m k Q hcount v
  simp [evenSuspensionSignTable, hne]

end Hypertournaments
