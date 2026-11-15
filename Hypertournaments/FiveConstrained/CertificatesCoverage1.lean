import Hypertournaments.FiveConstrained.CertificatesCoverage0

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem certificate_coverage_chunk_1 :
    (List.range 128).all (fun c => certificateCovered (128 + c)) = true := by
  rfl

end Hypertournaments.FiveConstrained
