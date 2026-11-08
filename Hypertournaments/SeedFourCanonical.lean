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

/-- The finite table computation without sorting-permutation overhead. -/
theorem seed4_base_signTable_canonical :
    ∀ Q : Finset (Fin 7), canonicalSignCentral4At seed4BaseSigns Q := by
  unfold canonicalSignCentral4At increasingPacketPositiveCount
  decide

/-- The sign-table calculation transfers to the actual intrinsic
hypertournament on every increasing five-tuple. -/
theorem seed4_base_canonicalCentral :
    ∀ Q : Finset (Fin 7), canonicalCentral4At seed4Base Q := by
  intro Q
  by_cases h : Q.card = 5
  · have ht := seed4_base_signTable_canonical Q
    simp only [canonicalSignCentral4At, dif_pos h] at ht
    simp only [canonicalCentral4At, dif_pos h]
    change localIndex (Hyper.fromOrderedSigns seed4BaseSigns)
      (Q.orderEmbOfFin h).toEmbedding = 2
    rw [localIndex_ordered_sign]
    exact ht
  · simp [canonicalCentral4At, h]

end Hypertournaments
