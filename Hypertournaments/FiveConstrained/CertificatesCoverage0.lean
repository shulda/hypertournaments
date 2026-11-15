import Hypertournaments.FiveConstrained.CertificatesData

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem certificate_coverage_chunk_0 :
    (List.range 128).all (fun c => certificateCovered (0 + c)) = true := by
  rfl

end Hypertournaments.FiveConstrained
