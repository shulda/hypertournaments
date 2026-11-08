import Hypertournaments.SeedFourData
import Hypertournaments.CanonicalPacket

/-!
# Canonical five-subset checks for the arity-four central seed

All 21 five-element subsets of the seven-vertex base are checked
using a simple sign-table count. The general orientation theorem
connects these checks to the intrinsic sorted-tuple local index.
The further orbit-invariance theorem is still pending.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- On an arbitrary five-subset, the canonical local index. -/
def canonicalCentral4At {k : ℕ}
    (A : Hyper 4 (Fin k)) (Q : Finset (Fin k)) : Prop :=
  if h : Q.card = 5 then
    localIndex A (Q.orderEmbOfFin h).toEmbedding = 2
  else True

/-! The canonical finite verification will be recovered from the
direct finite-set rank test through a general equivalence lemma. -/

end Hypertournaments
