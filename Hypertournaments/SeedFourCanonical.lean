import Hypertournaments.SeedFourData

/-!
# Canonical five-subset checks for the arity-four central seed

We certify the source sign tables first on *increasing* five-tuples,
one per five-element subset. The separate orbit-invariance theorem
will eventually upgrade these checks to full `Admissible`.

This module is deliberately finite and uses kernel-checked `decide`.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- For a five-element subset of Fin k, evaluate the intrinsic
hypertournament local index using its unique increasing enumeration. -/
def canonicalCentral4At {k : ℕ}
    (A : Hyper 4 (Fin k)) (Q : Finset (Fin k)) : Prop :=
  if h : Q.card = 5 then
    localIndex A (Q.orderEmbOfFin h).toEmbedding = 2
  else True

/-- All 21 canonical five-sets in the seven-vertex base are central.
The executable check ranges over all 128 subsets (vacuously for
those of size other than five). -/
theorem seed4_base_canonicalCentral :
    ∀ Q : Finset (Fin 7), canonicalCentral4At seed4Base Q := by
  unfold canonicalCentral4At
  decide

end Hypertournaments
