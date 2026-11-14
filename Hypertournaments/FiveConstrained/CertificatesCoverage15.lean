import Hypertournaments.FiveConstrained.CertificatesCoverage14

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem certificate_coverage_chunk_15 :
    (List.range 128).all (fun c => certificateCovered (1920 + c)) = true := by
  rfl

end Hypertournaments.FiveConstrained
