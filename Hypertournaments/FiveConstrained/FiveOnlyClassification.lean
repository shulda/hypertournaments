import Hypertournaments.FiveConstrained.Classification
import Lean.Elab.Tactic.Omega

/-!
# Exact classification with only five-vertex constraints

Source: `tex_hypertournaments` at
`64a392aa2b0e497c297f1218be3f1a8761bae18d`, classification supplement,
`rem:five-only`. Every four-vertex structure is admitted in this convention.
The full four/five classification therefore leaves only the `P9`-free and
unrestricted classes, rather than all five normalized positive palettes.
-/

namespace Hypertournaments.FiveConstrained

private theorem unrestricted_four_consistent (five : ℕ) : Consistent 7 five := by
  intro t _ht e
  have hbits : ∀ i : Fin 3, (7 : ℕ).testBit i.val = true := by decide
  exact hbits ⟨localIndex (maskHyper 5 (representative t)) e, by
    have hle : localIndex (maskHyper 5 (representative t)) e ≤ 2 := localIndex_le_central _ _
    omega⟩

/-- The literal five-only class is unbounded exactly when it admits `P0`. -/
theorem five_only_unbounded_iff (palette : ℕ) :
    (fiveOnlyClass palette).Unbounded ↔ palette.testBit 0 = true := by
  have hclass : fiveOnlyClass palette = constrainedClass 7 palette := by
    funext m A
    exact propext (constrained_seven_iff_fiveOnly A).symm
  rw [hclass, constrainedClass_unbounded_iff]
  exact ⟨And.right, fun h => ⟨by decide, h⟩⟩

/-- Among unbounded literal five-only classes, ordinary AP holds exactly
for omission of `P9` and for the unrestricted class. -/
theorem five_only_hasAP_iff {palette : ℕ} (hvalid : palette < 4096)
    (hU : (fiveOnlyClass palette).Unbounded) :
    (fiveOnlyClass palette).HasAP ↔ palette = 3583 ∨ palette = 4095 := by
  have hzero := (five_only_unbounded_iff palette).mp hU
  have hclass : (constrainedClass 7 palette).HasAP ↔ (fiveOnlyClass palette).HasAP :=
    FiniteClass.hasAP_congr (fun _ A => constrained_seven_iff_fiveOnly (palette := palette) A)
  have hU' : (constrainedClass 7 palette).Unbounded :=
    (constrainedClass_unbounded_iff 7 palette).mpr ⟨by decide, hzero⟩
  rw [← hclass, constrained_amalgamation_classification hvalid
    (unrestricted_four_consistent palette) hU']
  constructor
  · rintro ⟨hn, hp⟩
    have hs : palette = 1 ∨ palette = 119 ∨ palette = 257 ∨
        palette = 3583 ∨ palette = 4095 := by
      simpa [certificatePositive, Bool.or_eq_true, or_assoc] using hp
    rcases hs with rfl | rfl | rfl | h | h
    · exact False.elim ((by decide : (certificateSupport4 1).testBit 0 ≠ true)
        ((hn 0 (by decide)).mp (by decide)))
    · exact False.elim ((by decide : (certificateSupport4 119).testBit 0 ≠ true)
        ((hn 0 (by decide)).mp (by decide)))
    · exact False.elim ((by decide : (certificateSupport4 257).testBit 1 ≠ true)
        ((hn 1 (by decide)).mp (by decide)))
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    all_goals refine ⟨?_, by decide⟩
    all_goals intro d hd
    all_goals have hs : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    all_goals rcases hs with rfl | rfl | rfl <;> decide

/-- The two positive literal five-only cases have strong amalgamation. -/
theorem five_only_hasAP_iff_hasSAP {palette : ℕ} (hvalid : palette < 4096)
    (hU : (fiveOnlyClass palette).Unbounded) :
    (fiveOnlyClass palette).HasAP ↔ (fiveOnlyClass palette).HasSAP := by
  have hzero := (five_only_unbounded_iff palette).mp hU
  have hU' : (constrainedClass 7 palette).Unbounded :=
    (constrainedClass_unbounded_iff 7 palette).mpr ⟨by decide, hzero⟩
  have hAP : (constrainedClass 7 palette).HasAP ↔ (fiveOnlyClass palette).HasAP :=
    FiniteClass.hasAP_congr (fun _ A => constrained_seven_iff_fiveOnly (palette := palette) A)
  have hSAP : (constrainedClass 7 palette).HasSAP ↔ (fiveOnlyClass palette).HasSAP :=
    FiniteClass.hasSAP_congr (fun _ A => constrained_seven_iff_fiveOnly (palette := palette) A)
  exact hAP.symm.trans
    ((constrained_hasAP_iff_hasSAP hvalid (unrestricted_four_consistent palette) hU').trans hSAP)

/-- A single iff includes both the actual unboundedness condition and AP. -/
theorem five_only_unbounded_amalgamation_iff {palette : ℕ} (hvalid : palette < 4096) :
    ((fiveOnlyClass palette).Unbounded ∧ (fiveOnlyClass palette).HasAP) ↔
      palette = 3583 ∨ palette = 4095 := by
  constructor
  · rintro ⟨hU, hAP⟩
    exact (five_only_hasAP_iff hvalid hU).mp hAP
  · intro hp
    have hzero : palette.testBit 0 = true := by
      rcases hp with rfl | rfl <;> decide
    have hU := (five_only_unbounded_iff palette).mpr hzero
    exact ⟨hU, (five_only_hasAP_iff hvalid hU).mpr hp⟩

end Hypertournaments.FiveConstrained
