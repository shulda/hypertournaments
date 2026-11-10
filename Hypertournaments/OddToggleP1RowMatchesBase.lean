import Hypertournaments.OddToggleP1CoreRowParity
import Hypertournaments.OddToggleP1ExplicitSides
import Hypertournaments.OddToggleP1PadRowFromSplit
import Hypertournaments.OddToggleP1PadCorePartition

/-!
# Matching the actual p1 canonical link rows with their base facet signs

The complete certified pad and core row counts imply every left
one-point packet has matching base-sign parity, as does every right
one-point packet except those omitting protected a0 and a4.
The latter two are treated by normalized homogeneous signs.
-/

namespace Hypertournaments

theorem p1BaseVertexBit_pad (k : ℕ)
    (s : Fin (2*(2*k))) :
    p1BaseVertexBit k (p1PadAt k s) = true := by
  simp [p1BaseVertexBit, p1PadAt_lt]

theorem p1BaseVertexBit_core (k : ℕ) (j : Fin 6) :
    p1BaseVertexBit k (p1CoreAt k j) = p1CoreBaseBit j := by
  fin_cases j <;>
    simp [p1BaseVertexBit, p1CoreAt, p1CoreBaseBit] <;>
    omega

/-- The parity of every left canonical link row equals the bit
prescribed on the omitted old facet of the common base. -/
theorem p1CanonicalLeft_row_matches_base (k : ℕ)
    (v : Fin (4*k+6)) :
    p1CanonicalRowPositiveCount k true v % 2 =
      (if p1BaseVertexBit k v then 1 else 0) := by
  rcases p1OldVertex_pad_or_core k v with ⟨s, rfl⟩ | ⟨j, rfl⟩
  · rw [p1CanonicalPad_rowParity]
    simp [p1BaseVertexBit_pad]
  · rw [p1CanonicalCore_rowParity]
    simp [p1BaseVertexBit_core]

/-- On the right, the only unmatched link-row parities are at
the two protected core vertices a0 and a4. -/
theorem p1CanonicalRight_row_matches_base_unprotected (k : ℕ)
    (v : Fin (4*k+6))
    (hzero : v ≠ p1CoreAt k (0 : Fin 6))
    (hfour : v ≠ p1CoreAt k (4 : Fin 6)) :
    p1CanonicalRowPositiveCount k false v % 2 =
      (if p1BaseVertexBit k v then 1 else 0) := by
  rcases p1OldVertex_pad_or_core k v with ⟨s, rfl⟩ | ⟨j, rfl⟩
  · rw [p1CanonicalPad_rowParity]
    simp [p1BaseVertexBit_pad]
  · have hjzero : j ≠ 0 := by
      intro hz
      subst j
      exact hzero rfl
    have hjfour : j ≠ 4 := by
      intro hf
      subst j
      exact hfour rfl
    rw [p1CanonicalCore_rowParity]
    cases hb : p1CoreBaseBit j <;>
      simp [p1BaseVertexBit_core, hjzero, hjfour, hb]

end Hypertournaments
