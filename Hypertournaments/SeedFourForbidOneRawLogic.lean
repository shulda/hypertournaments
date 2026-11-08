import Hypertournaments.SeedFourForbidOneLogic

/-!
# Unpacked 15-Boolean unsatisfiability certificate

This is the same twenty local constraints as in
`forbidOne_fifteen_bit_unsat`, but expressed directly on fifteen
Boolean inputs rather than via a 10-bit/5-bit numerical encoding.

There is no reliance on source tuple orientations here. The point is
to allow a later semantic proof to substitute those orientations
directly without proving separate bit-packing arithmetic lemmas.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Indices 0..9 stand for 12,13,14,15,23,24,25,34,35,45.
Indices 10..14 stand for 01,02,03,04,05. -/
def rawTopOk (b : Fin 15 → Bool) : Bool :=
  ruleT  (b 0) (b 1) (b 4) &&
  ruleT  (b 0) (b 2) (b 5) &&
  ruleT  (b 0) (b 3) (b 6) &&
  ruleCm (b 1) (b 2) (b 7) &&
  ruleCp (b 1) (b 3) (b 8) &&
  ruleT  (b 2) (b 3) (b 9) &&
  ruleT  (b 4) (b 5) (b 7) &&
  ruleCp (b 4) (b 6) (b 8) &&
  ruleCm (b 5) (b 6) (b 9) &&
  ruleT  (b 7) (b 8) (b 9)

/-- Ten additional constraints involving base vertex 0. -/
def rawOuterOk (b : Fin 15 → Bool) : Bool :=
  ruleCm (b 10) (b 11) (b 0) &&
  ruleT  (b 10) (b 12) (b 1) &&
  ruleT  (b 10) (b 13) (b 2) &&
  ruleT  (b 10) (b 14) (b 3) &&
  ruleT  (b 11) (b 12) (b 4) &&
  ruleT  (b 11) (b 13) (b 5) &&
  ruleT  (b 11) (b 14) (b 6) &&
  ruleCm (b 12) (b 13) (b 7) &&
  ruleT  (b 12) (b 14) (b 8) &&
  ruleCm (b 13) (b 14) (b 9)

/-- All 2^15 bit assignments are impossible. The already certified
17-pattern factorization in `SeedFourForbidOneLogic` remains available
as the human-readable compact certificate. -/
theorem no_raw_forbidOne_assignment :
    ∀ b : Fin 15 → Bool, rawTopOk b = true → rawOuterOk b = true → False := by
  decide +kernel

end Hypertournaments
