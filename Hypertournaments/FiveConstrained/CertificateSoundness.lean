import Hypertournaments.FiveConstrained.CertificateLogic
import Hypertournaments.FiveConstrained.CertificatePackets
import Hypertournaments.FiveConstrained.Classes
import Hypertournaments.FiveConstrained.ClassRecognition

/-!
# From finite Boolean certificates to failure of ordinary amalgamation

The checker is related to actual local induced structures. Any hypothetical
amalgam restricts to the canonical one-point union; its mixed bits reconstruct
all of its intrinsic orientations. Thus the finite computation rules out
arbitrarily large ordinary amalgams, not just the displayed finite carrier.
-/

namespace Hypertournaments.FiveConstrained

theorem certificate_side_constrained (palette : ℕ) (d : CertificateDiagram)
    (h : certificateAccepts palette (certificateSideRequirements d) = true)
    (rightSide : Bool) :
    Constrained (certificateSupport4 palette) palette (d.sideHyper rightSide) := by
  obtain ⟨hfour, hfive⟩ := (certificateSideRequirements_iff palette d).mp h
  have hb : rightSide ∈ [false, true] := by cases rightSide <;> simp
  apply (constrained_iff_increasing _ _ _).mpr
  constructor
  · intro e he
    have hq : ((e 0).val, (e 1).val, (e 2).val, (e 3).val) ∈
        certificateFourSets (d.baseSize + 1) := by
      apply (mem_certificateFourSets _ _ _ _ _).mpr
      exact ⟨(e 0).isLt, (e 1).isLt, (e 2).isLt, (e 3).isLt,
        he (by decide), he (by decide), he (by decide)⟩
    rw [d.side_localIndex rightSide e he]
    exact hfour rightSide hb _ hq
  · intro e he
    apply (packetAllowed_iff_type5 palette _).mpr
    rw [← packet5OfHyper_eq_encode5, d.side_packet5 rightSide e he]
    apply hfive rightSide hb
    apply (mem_certificateFiveSets _ _ _ _ _ _).mpr
    exact ⟨(e 0).isLt, (e 1).isLt, (e 2).isLt, (e 3).isLt, (e 4).isLt,
      he (by decide), he (by decide), he (by decide), he (by decide)⟩

theorem certificate_joint_accepts_mixed (palette : ℕ) (d : CertificateDiagram)
    (x : ℕ)
    (h : Constrained (certificateSupport4 palette) palette (d.jointHyper x)) :
    certificateAccepts palette (certificateMixedRequirements d x) = true := by
  apply (certificateMixedRequirements_iff palette d x).mpr
  constructor
  · rintro ⟨a, b⟩ hq
    obtain ⟨ha, hb, hab⟩ := (mem_certificatePairs _ _ _).mp hq
    let a' : Fin d.baseSize := ⟨a, ha⟩
    let b' : Fin d.baseSize := ⟨b, hb⟩
    have hab' : a' < b' := hab
    have hallowed := h.1 (d.mixed_fourTuple a' b' hab')
    change (certificateSupport4 palette).testBit
      (localIndex (d.jointHyper x) (d.mixed_fourTuple a' b' hab')) = true at hallowed
    rw [d.mixed_localIndex x a' b' hab'] at hallowed
    exact hallowed
  · rintro ⟨a, b, c⟩ hq
    obtain ⟨ha, hb, hc, hab, hbc⟩ := (mem_certificateTriples _ _ _ _).mp hq
    let a' : Fin d.baseSize := ⟨a, ha⟩
    let b' : Fin d.baseSize := ⟨b, hb⟩
    let c' : Fin d.baseSize := ⟨c, hc⟩
    have hab' : a' < b' := hab
    have hbc' : b' < c' := hbc
    have hallowed := (packetAllowed_iff_type5 palette _).mp
      (h.2 (d.mixed_fiveTuple a' b' c' hab' hbc'))
    rw [← packet5OfHyper_eq_encode5, d.mixed_packet5 x a' b' c' hab' hbc'] at hallowed
    exact hallowed

/-- General semantic soundness, with actual side disagreement exposed. The
finite certificate library separately proves this disagreement for every
retained diagram, thereby discharging the identification branch. -/
theorem certificateCheck_not_hasAP (palette : ℕ) (d : CertificateDiagram)
    (hcheck : certificateCheck palette d = true)
    (hdisagree : ∃ t : Fin 3 ↪ Fin (d.baseSize + 1),
      (d.sideHyper false).orient t ≠ (d.sideHyper true).orient t) :
    ¬ (normalizedClass palette).HasAP := by
  obtain ⟨_hne, hside, hmixed⟩ := (certificateCheck_iff palette d).mp hcheck
  have hL := certificate_side_constrained palette d hside false
  have hR := certificate_side_constrained palette d hside true
  have hA : normalizedClass palette d.baseSize d.baseHyper :=
    Constrained.of_preserves (onePointBaseEmbedding d.baseSize) (d.base_side false) hL
  apply FiniteClass.not_hasAP_of_no_joint (normalizedClass_hereditary palette)
    d.baseHyper (d.sideHyper false) (d.sideHyper true) hA hL hR
    (d.base_side false) (d.base_side true) hdisagree
  intro E hE hEL hER
  let x := d.mixedMask E
  have hpres : Preserves (d.jointHyper x) E (Function.Embedding.refl _) := by
    intro t
    simpa only [Function.Embedding.trans_refl] using d.joint_recovery E hEL hER t
  have hJ := Constrained.of_preserves (Function.Embedding.refl _) hpres hE
  have haccept := certificate_joint_accepts_mixed palette d x hJ
  have hreject := hmixed x (d.mixedMask_lt E)
  rw [haccept] at hreject
  exact Bool.noConfusion hreject

/-- Concrete bounded link masks supply the actual disagreement needed by the
ordinary-AP theorem. These size bounds are checked for every stored diagram. -/
theorem certificateCheck_not_hasAP_of_bounded (palette : ℕ) (d : CertificateDiagram)
    (hcheck : certificateCheck palette d = true)
    (hm : d.baseSize ≤ 7)
    (hl : d.left < 2 ^ (d.baseSize.choose 2))
    (hr : d.right < 2 ^ (d.baseSize.choose 2)) :
    ¬ (normalizedClass palette).HasAP := by
  apply certificateCheck_not_hasAP palette d hcheck
  exact d.side_disagree hm hl hr ((certificateCheck_iff palette d).mp hcheck).1

end Hypertournaments.FiveConstrained
