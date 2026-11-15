import Hypertournaments.FiveConstrained.CertificatesProfiles0
import Hypertournaments.FiveConstrained.CertificatesProfiles1
import Hypertournaments.FiveConstrained.CertificatesProfiles2
import Hypertournaments.FiveConstrained.CertificatesProfiles3
import Hypertournaments.FiveConstrained.CertificatesProfiles4
import Hypertournaments.FiveConstrained.CertificatesProfiles5
import Hypertournaments.FiveConstrained.CertificatesProfiles6
import Hypertournaments.FiveConstrained.CertificatesProfiles7
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem certificate_profiles (i : Fin 37) :
    certificateProfile (certificateDiagram i) = certificateStoredProfile i := by
  fin_cases i
  · exact certificate_profile_0
  · exact certificate_profile_1
  · exact certificate_profile_2
  · exact certificate_profile_3
  · exact certificate_profile_4
  · exact certificate_profile_5
  · exact certificate_profile_6
  · exact certificate_profile_7
  · exact certificate_profile_8
  · exact certificate_profile_9
  · exact certificate_profile_10
  · exact certificate_profile_11
  · exact certificate_profile_12
  · exact certificate_profile_13
  · exact certificate_profile_14
  · exact certificate_profile_15
  · exact certificate_profile_16
  · exact certificate_profile_17
  · exact certificate_profile_18
  · exact certificate_profile_19
  · exact certificate_profile_20
  · exact certificate_profile_21
  · exact certificate_profile_22
  · exact certificate_profile_23
  · exact certificate_profile_24
  · exact certificate_profile_25
  · exact certificate_profile_26
  · exact certificate_profile_27
  · exact certificate_profile_28
  · exact certificate_profile_29
  · exact certificate_profile_30
  · exact certificate_profile_31
  · exact certificate_profile_32
  · exact certificate_profile_33
  · exact certificate_profile_34
  · exact certificate_profile_35
  · exact certificate_profile_36


theorem certificate_links_unequal (i : Fin 37) :
    (certificateDiagram i).left ≠ (certificateDiagram i).right := by
  revert i
  decide +kernel

theorem certificate_bounds (i : Fin 37) :
    3 ≤ (certificateDiagram i).baseSize ∧
      (certificateDiagram i).baseSize ≤ 7 ∧
      (certificateDiagram i).base < 2 ^ ((certificateDiagram i).baseSize.choose 3) ∧
      (certificateDiagram i).left < 2 ^ ((certificateDiagram i).baseSize.choose 2) ∧
      (certificateDiagram i).right < 2 ^ ((certificateDiagram i).baseSize.choose 2) := by
  revert i
  decide +kernel

end Hypertournaments.FiveConstrained
