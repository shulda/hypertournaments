import Hypertournaments.FiveConstrained.CertificatesCoverage0
import Hypertournaments.FiveConstrained.CertificatesCoverage1
import Hypertournaments.FiveConstrained.CertificatesCoverage2
import Hypertournaments.FiveConstrained.CertificatesCoverage3
import Hypertournaments.FiveConstrained.CertificatesCoverage4
import Hypertournaments.FiveConstrained.CertificatesCoverage5
import Hypertournaments.FiveConstrained.CertificatesCoverage6
import Hypertournaments.FiveConstrained.CertificatesCoverage7
import Hypertournaments.FiveConstrained.CertificatesCoverage8
import Hypertournaments.FiveConstrained.CertificatesCoverage9
import Hypertournaments.FiveConstrained.CertificatesCoverage10
import Hypertournaments.FiveConstrained.CertificatesCoverage11
import Hypertournaments.FiveConstrained.CertificatesCoverage12
import Hypertournaments.FiveConstrained.CertificatesCoverage13
import Hypertournaments.FiveConstrained.CertificatesCoverage14
import Hypertournaments.FiveConstrained.CertificatesCoverage15
import Hypertournaments.FiveConstrained.CertificatesProfiles
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Omega

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem certificate_coverage (c : Fin 2048) :
    certificatePositive (2 * c.val + 1) = true ∨
      certificateBlocks (2 * c.val + 1)
        (certificateStoredProfile (certificateChoice c)) = true := by
  have hchunks (q : Fin 16) (r : Fin 128) :
      certificateCovered (128 * q.val + r.val) = true := by
    fin_cases q
    · exact List.all_eq_true.mp certificate_coverage_chunk_0 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_1 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_2 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_3 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_4 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_5 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_6 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_7 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_8 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_9 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_10 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_11 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_12 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_13 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_14 r.val (List.mem_range.mpr r.isLt)
    · exact List.all_eq_true.mp certificate_coverage_chunk_15 r.val (List.mem_range.mpr r.isLt)
  have hq : c.val / 128 < 16 := by omega
  have hr : c.val % 128 < 128 := Nat.mod_lt _ (by decide)
  have h := hchunks ⟨c.val / 128, hq⟩ ⟨c.val % 128, hr⟩
  have hc : certificateCovered c.val = true := by
    simpa only [Nat.div_add_mod] using h
  simpa only [certificateCovered, Nat.mod_eq_of_lt c.isLt, Bool.or_eq_true] using hc

theorem certificate_full_coverage (c : Fin 2048) :
    certificatePositive (2 * c.val + 1) = true ∨
      certificateCheck (2 * c.val + 1)
        (certificateDiagram (certificateChoice c)) = true := by
  rcases certificate_coverage c with h | h
  · exact Or.inl h
  · right
    simp only [certificateCheck, Bool.and_eq_true, decide_eq_true_eq,
      certificate_profiles]
    exact ⟨certificate_links_unequal _, h⟩

/-- Every negative normalized palette has a concrete checked one-point
obstruction. Soundness for intrinsic ordinary AP is proved separately. -/
theorem exists_certificate (c : Fin 2048)
    (hnegative : certificatePositive (2 * c.val + 1) = false) :
    ∃ i : Fin 37, certificateCheck (2 * c.val + 1) (certificateDiagram i) = true := by
  have h := certificate_full_coverage c
  simp only [hnegative, Bool.false_eq_true, false_or] at h
  exact ⟨certificateChoice c, h⟩

end Hypertournaments.FiveConstrained
