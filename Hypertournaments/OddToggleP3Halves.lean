import Hypertournaments.OddToggleP3ExplicitPotentials

/-!
# Exact complementary eligible/protected half-blocks for the p3 span

The random p3 obstruction partitions m=4k+2 old blocks into two
consecutive halves. The left-side link potential is supported on
one-block-missing transversals with missing block in the LOWER half;
the right side uses the UPPER half. To certify genuine side
admissibility when all old blocks occur, each side protects the
OPPOSITE half.

Both half-sets are explicit finite label sets, disjoint. When k≥1,
each protected half contains three consecutive labels: 0,1,2
in the lower half and m/2,m/2+1,m/2+2 in the upper half.
This provides the quantitative hypotheses required by the
real protected-triple side-packet theorem without any extra
relation or order in the hypertournament language.
-/

namespace Hypertournaments

def p3EligibleLowerHalf (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.val < m/2)

def p3EligibleUpperHalf (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => m/2 ≤ i.val)

theorem p3EligibleHalves_disjoint (m : ℕ) :
    Disjoint (p3EligibleLowerHalf m) (p3EligibleUpperHalf m) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hlo : i.val < m/2 := (Finset.mem_filter.mp hi).2
  have hup : m/2 ≤ i.val := (Finset.mem_filter.mp hj).2
  omega

/-- The three lowest block labels are protected for a side whose
eligible missing-block indices lie in the upper half. -/
theorem p3LowerProtectedTriple
    (k : ℕ) (hk : 1 ≤ k) :
    (0:ℕ)+2 < 4*k+2 ∧
    ∀ b : Fin (4*k+2),
      (0:ℕ) ≤ b.val → b.val ≤ 2 →
      b ∈ p3EligibleLowerHalf (4*k+2) := by
  constructor
  · omega
  intro b _ hb
  have hHalf : 3 ≤ (4*k+2)/2 := by omega
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by omega⟩

/-- The first three upper-half indices are protected for a side
whose eligible missing-block indices lie in the lower half. -/
theorem p3UpperProtectedTriple
    (k : ℕ) (hk : 1 ≤ k) :
    (4*k+2)/2+2 < 4*k+2 ∧
    ∀ b : Fin (4*k+2),
      (4*k+2)/2 ≤ b.val →
        b.val ≤ (4*k+2)/2+2 →
      b ∈ p3EligibleUpperHalf (4*k+2) := by
  constructor
  · omega
  intro b hb _
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hb⟩

end Hypertournaments
