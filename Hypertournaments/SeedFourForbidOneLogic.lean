import Hypertournaments.SeedFourPacket

/-!
# The seventeen-case Boolean certificate for omitting T_{4,1}

This is the *purely finite combinatorial* contradiction from the
technical note. A normalized five-packet of type T_{4,1} is forbidden.

The ten mixed orientations on pairs of old vertices 1..5 are
encoded by a 10-bit number. Exactly seventeen of the 1024
assignments survive the ten corresponding triangle constraints.
For none of those seventeen assignments are the remaining five
bits (pairs 0i, i=1..5) compatible with the ten other constraints.

This is a small proof-by-reflection, not an external SAT solver.
The semantic link to actual hyperturnaj orientation is separate.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def tripleCode (a b c : Bool) : ℕ :=
  (if a then 4 else 0) + (if b then 2 else 0) +
    (if c then 1 else 0)

/-- Rule T forbids bit triples 010 and 101. -/
def ruleT (a b c : Bool) : Bool :=
  let v := tripleCode a b c
  decide (v ≠ 2 ∧ v ≠ 5)

/-- Rule C-minus forbids 001, 100, 111. -/
def ruleCm (a b c : Bool) : Bool :=
  let v := tripleCode a b c
  decide (v ≠ 1 ∧ v ≠ 4 ∧ v ≠ 7)

/-- Rule C-plus forbids 000, 011, 110. -/
def ruleCp (a b c : Bool) : Bool :=
  let v := tripleCode a b c
  decide (v ≠ 0 ∧ v ≠ 3 ∧ v ≠ 6)

/-- Ten pair bits on the old vertices 1..5; their indices are
12,13,14,15,23,24,25,34,35,45 in that order. -/
def topBit (u : Fin 1024) (i : ℕ) : Bool :=
  Nat.testBit u.val i

/-- Five pair bits 01,02,03,04,05. -/
def bottomBit (v : Fin 32) (i : ℕ) : Bool :=
  Nat.testBit v.val i

/-- All ten constraints internal to the five vertices 1..5. -/
def topOk (u : Fin 1024) : Bool :=
  ruleT (topBit u 0) (topBit u 1) (topBit u 4) &&
  ruleT (topBit u 0) (topBit u 2) (topBit u 5) &&
  ruleT (topBit u 0) (topBit u 3) (topBit u 6) &&
  ruleCm (topBit u 1) (topBit u 2) (topBit u 7) &&
  ruleCp (topBit u 1) (topBit u 3) (topBit u 8) &&
  ruleT (topBit u 2) (topBit u 3) (topBit u 9) &&
  ruleT (topBit u 4) (topBit u 5) (topBit u 7) &&
  ruleCp (topBit u 4) (topBit u 6) (topBit u 8) &&
  ruleCm (topBit u 5) (topBit u 6) (topBit u 9) &&
  ruleT (topBit u 7) (topBit u 8) (topBit u 9)

/-- The remaining ten constraints involving vertex zero. -/
def outerOk (u : Fin 1024) (v : Fin 32) : Bool :=
  ruleCm (bottomBit v 0) (bottomBit v 1) (topBit u 0) &&
  ruleT (bottomBit v 0) (bottomBit v 2) (topBit u 1) &&
  ruleT (bottomBit v 0) (bottomBit v 3) (topBit u 2) &&
  ruleT (bottomBit v 0) (bottomBit v 4) (topBit u 3) &&
  ruleT (bottomBit v 1) (bottomBit v 2) (topBit u 4) &&
  ruleT (bottomBit v 1) (bottomBit v 3) (topBit u 5) &&
  ruleT (bottomBit v 1) (bottomBit v 4) (topBit u 6) &&
  ruleCm (bottomBit v 2) (bottomBit v 3) (topBit u 7) &&
  ruleT (bottomBit v 2) (bottomBit v 4) (topBit u 8) &&
  ruleCm (bottomBit v 3) (bottomBit v 4) (topBit u 9)

/-- The seventeen surviving ten-bit assignments, proof-mined
from the four-ary central-type obstruction. -/
def topPatterns : Finset (Fin 1024) :=
  {23,77,205,236,237,387,389,498,500,584,585,589,816,831,848,863,946}

/-- All 1024 possible internal assignments are checked. -/
theorem topOk_iff_pattern (u : Fin 1024) :
    topOk u = true ↔ u ∈ topPatterns := by
  decide +kernel

/-- Each of the 17 surviving patterns has no compatible assignment
of the five edges incident with vertex zero. -/
theorem no_bottom_for_pattern (u : Fin 1024) (hu : u ∈ topPatterns)
    (v : Fin 32) : outerOk u v = false := by
  revert u v
  decide +kernel

/-- Complete Boolean contradiction for the entire 15-bit
mixed-link assignment. -/
theorem forbidOne_fifteen_bit_unsat (u : Fin 1024) (v : Fin 32)
    (hu : topOk u = true) (hv : outerOk u v = true) : False := by
  have hp : u ∈ topPatterns := (topOk_iff_pattern u).mp hu
  have hn := no_bottom_for_pattern u hp v
  rw [hn] at hv
  cases hv

end Hypertournaments
