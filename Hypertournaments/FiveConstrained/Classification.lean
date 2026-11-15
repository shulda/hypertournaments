import Hypertournaments.FiveConstrained.CertificateSoundness
import Hypertournaments.FiveConstrained.CertificatesCoverage
import Hypertournaments.FiveConstrained.Positive
import Hypertournaments.FiveConstrained.Unbounded

/-!
# Complete five-constrained ternary amalgamation classification

The finite certificates are connected to actual ordinary AP. The five
positive cases have independently constructed strong amalgams. Presentations
with separate four/five conditions are normalized by a proved consequence
of ordinary AP and actual unboundedness.
-/

namespace Hypertournaments.FiveConstrained

/-- Every other unbounded valid five-palette has a concrete intrinsic
one-point obstruction to ordinary AP. -/
theorem normalized_not_hasAP {palette : ℕ} (hvalid : palette < 4096)
    (hzero : palette.testBit 0 = true)
    (hnegative : certificatePositive palette = false) :
    ¬ (normalizedClass palette).HasAP := by
  have hodd : palette % 2 = 1 := (Nat.mod_two_eq_one_iff_testBit_zero).mpr hzero
  let c : Fin 2048 := ⟨palette / 2, by omega⟩
  have hc : 2 * c.val + 1 = palette := by
    dsimp [c]
    omega
  have hnegative' : certificatePositive (2 * c.val + 1) = false := by
    simpa only [hc] using hnegative
  obtain ⟨i, hi⟩ := exists_certificate c hnegative'
  rw [hc] at hi
  obtain ⟨_hlower, hupper, _hbase, hleft, hright⟩ := certificate_bounds i
  exact certificateCheck_not_hasAP_of_bounded palette (certificateDiagram i)
    hi hupper hleft hright

/-- Precisely the five advertised normalized unbounded palettes have ordinary AP. -/
theorem normalized_hasAP_iff {palette : ℕ} (hvalid : palette < 4096)
    (hzero : palette.testBit 0 = true) :
    (normalizedClass palette).HasAP ↔ certificatePositive palette = true := by
  constructor
  · intro hAP
    cases hp : certificatePositive palette
    · exact False.elim (normalized_not_hasAP hvalid hzero hp hAP)
    · rfl
  · intro hp
    exact (normalized_positive_hasSAP hp).hasAP

/-- In every normalized unbounded case AP and SAP agree, with both
directions proved using the original intrinsic embeddings. -/
theorem normalized_hasAP_iff_hasSAP {palette : ℕ} (hvalid : palette < 4096)
    (hU : (normalizedClass palette).Unbounded) :
    (normalizedClass palette).HasAP ↔ (normalizedClass palette).HasSAP := by
  constructor
  · intro hAP
    exact normalized_positive_hasSAP
      ((normalized_hasAP_iff hvalid ((normalizedClass_unbounded_iff palette).mp hU)).mp hAP)
  · exact FiniteClass.HasSAP.hasAP

/-- The complete classification with actual unboundedness as its premise. -/
theorem normalized_unbounded_amalgamation_classification {palette : ℕ}
    (hvalid : palette < 4096) (hU : (normalizedClass palette).Unbounded) :
    (normalizedClass palette).HasAP ↔
      palette = 1 ∨ palette = 119 ∨ palette = 257 ∨
        palette = 3583 ∨ palette = 4095 := by
  rw [normalized_hasAP_iff hvalid ((normalizedClass_unbounded_iff palette).mp hU)]
  simp [certificatePositive, Bool.or_eq_true, or_assoc]

/-- Actual realized four-types of a normalized presentation. Bits above
index two do not name a four-vertex isomorphism type. -/
def NormalizedFour (four five : ℕ) : Prop :=
  ∀ d : ℕ, d ≤ 2 →
    (four.testBit d = true ↔ (certificateSupport4 five).testBit d = true)

/-- Arbitrary consistent unbounded four/five presentations have AP exactly
when their four-condition is normalized and their five-palette is positive. -/
theorem constrained_amalgamation_classification {four five : ℕ}
    (hvalid : five < 4096) (hconsistent : Consistent four five)
    (hU : (constrainedClass four five).Unbounded) :
    (constrainedClass four five).HasAP ↔
      NormalizedFour four five ∧ certificatePositive five = true := by
  constructor
  · intro hAP
    have hn : NormalizedFour four five := normalization_of_hasAP hconsistent hU hAP
    have hN : (normalizedClass five).HasAP :=
      (FiniteClass.hasAP_congr (fun _ A =>
        constrainedClass_iff_normalized_of_hasAP hconsistent hU hAP A)).mp hAP
    exact ⟨hn, (normalized_hasAP_iff hvalid (p0_of_unbounded_constrained hU)).mp hN⟩
  · rintro ⟨hn, hp⟩
    apply (FiniteClass.hasAP_congr (fun _ A =>
      constrained_iff_of_four_agree hn A)).mpr
    exact (normalized_positive_hasSAP hp).hasAP

/-- AP-to-SAP for the complete consistent unbounded five-constrained class. -/
theorem constrained_hasAP_iff_hasSAP {four five : ℕ}
    (hvalid : five < 4096) (hconsistent : Consistent four five)
    (hU : (constrainedClass four five).Unbounded) :
    (constrainedClass four five).HasAP ↔ (constrainedClass four five).HasSAP := by
  constructor
  · intro hAP
    obtain ⟨hn, hp⟩ :=
      (constrained_amalgamation_classification hvalid hconsistent hU).mp hAP
    apply (FiniteClass.hasSAP_congr (fun _ A =>
      constrained_iff_of_four_agree hn A)).mpr
    exact normalized_positive_hasSAP hp
  · exact FiniteClass.HasSAP.hasAP

/-- The later technical note's convention: only five-vertex conditions,
which are vacuous on every smaller carrier. -/
def fiveOnlyClass (palette : ℕ) : FiniteClass 3 := fun _ A => FiveAllowed palette A

theorem constrained_seven_iff_fiveOnly {palette : ℕ} {V : Type*} (A : Hyper 3 V) :
    Constrained 7 palette A ↔ FiveAllowed palette A := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro e
  have hbits : ∀ i : Fin 3, (7 : ℕ).testBit i.val = true := by decide
  exact hbits ⟨localIndex A e, by
    have hle : localIndex A e ≤ 2 := localIndex_le_central A e
    omega⟩

/-- Exact negative theorem of the uploaded November note. The five palettes
are exceptions to this necessary condition; their positive classification
is the normalized four/five theorem above. -/
theorem five_only_negative_classification {palette : ℕ} (hvalid : palette < 4096)
    (hzero : palette.testBit 0 = true) (hAP : (fiveOnlyClass palette).HasAP) :
    palette = 1 ∨ palette = 119 ∨ palette = 257 ∨
      palette = 3583 ∨ palette = 4095 := by
  have hclassAP : (constrainedClass 7 palette).HasAP :=
    (FiniteClass.hasAP_congr (fun _ A => constrained_seven_iff_fiveOnly A)).mpr hAP
  have hU : (constrainedClass 7 palette).Unbounded :=
    (constrainedClass_unbounded_iff 7 palette).mpr ⟨by decide, hzero⟩
  have hconsistent : Consistent 7 palette := by
    intro t _ht e
    have hbits : ∀ i : Fin 3, (7 : ℕ).testBit i.val = true := by decide
    exact hbits ⟨localIndex (maskHyper 5 (representative t)) e,
      by
        have hle : localIndex (maskHyper 5 (representative t)) e ≤ 2 :=
          localIndex_le_central (maskHyper 5 (representative t)) e
        omega⟩
  have hp := (constrained_amalgamation_classification hvalid hconsistent hU).mp hclassAP
  simpa [certificatePositive, Bool.or_eq_true, or_assoc] using hp.2

end Hypertournaments.FiveConstrained
