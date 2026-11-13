import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3OccupancyExcess

/-!
# One-excess and protected triple geometry for the p3 fresh-point side

In the case when all m old blocks occur in a one-fresh packet,
there are m+1 old vertices, hence exactly one excess vertex.
All occupancies are positive and at most one block is nonsingleton.

Any three consecutive protected labels therefore have occupancies
(a,b,c) with a,b,c≥1 and a+b+c≤4. The only possibilities are
(1,1,1), (2,1,1), (1,2,1), or (1,1,2). In every case there
are two singleton positions whose offset difference is odd:
adjacent singleton blocks if they exist, or the two flanking
singleton blocks around the doubled middle block, at distance 3.

These are finite numerical statements. The actual block-prefix
position identities and source-support/canonical-facet bridge
remain separate formalization steps.
-/

namespace Hypertournaments

/-- In a positive occupancy profile with m+extra vertices, at
most extra block labels can have occupancy above one. -/
theorem p3NonSingleton_count_le_excess
    (m extra : ℕ) (occ : Fin m → ℕ)
    (hall : ∀ i : Fin m, 0 < occ i)
    (htotal : (∑ i : Fin m, occ i) = m+extra) :
    (Finset.univ.filter (fun i : Fin m => 1 < occ i)).card ≤ extra := by
  classical
  let bad : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => 1 < occ i)
  have hpoint (i : Fin m) :
      1 + (if 1 < occ i then (1 : ℕ) else 0) ≤ occ i := by
    by_cases hb : 1 < occ i
    · simp only [if_pos hb]
      omega
    · simp only [if_neg hb]
      have hp := hall i
      omega
  have hsum :
      (∑ i : Fin m, ((1 : ℕ) + if 1 < occ i then 1 else 0)) ≤
        ∑ i : Fin m, occ i := by
    apply Finset.sum_le_sum
    intro i _
    exact hpoint i
  have hfilter :
      (∑ i : Fin m, (if 1 < occ i then (1 : ℕ) else 0)) =
        bad.card := by
    calc
      (∑ i : Fin m, (if 1 < occ i then (1 : ℕ) else 0)) =
          ∑ i ∈ (Finset.univ.filter (fun i : Fin m => 1 < occ i)),
            (1 : ℕ) := by
              rw [Finset.sum_filter]
      _ = bad.card := by simp [bad]
  have hsumEq :
      (∑ i : Fin m, ((1 : ℕ) + if 1 < occ i then 1 else 0)) =
        m + bad.card := by
    rw [Finset.sum_add_distrib, hfilter]
    simp
  rw [hsumEq, htotal] at hsum
  simpa only [bad] using (show bad.card ≤ extra by omega)

/-- Any positive triple whose occupancy sum is at most four
has adjacent singleton labels, or singleton/double/singleton. -/
theorem p3ProtectedTriple_patterns
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a+b+c ≤ 4) :
    (a=1 ∧ b=1) ∨
    (b=1 ∧ c=1) ∨
    (a=1 ∧ b=2 ∧ c=1) := by
  omega

/-- For every possible protected triple occupancy pattern and
every starting offset, there are two singleton vertices at
positions of opposite parity. -/
theorem p3ProtectedTriple_singletons_oppositeParity
    (start a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a+b+c ≤ 4) :
    (a=1 ∧ b=1 ∧ start%2 ≠ (start+a)%2) ∨
    (b=1 ∧ c=1 ∧ (start+a)%2 ≠ (start+a+b)%2) ∨
    (a=1 ∧ b=2 ∧ c=1 ∧
      start%2 ≠ (start+a+b)%2) := by
  rcases p3ProtectedTriple_patterns a b c ha hb hc hsum with
      ⟨ha1,hb1⟩ | ⟨hb1,hc1⟩ | ⟨ha1,hb2,hc1⟩
  · left
    exact ⟨ha1, hb1, by omega⟩
  · right
    left
    exact ⟨hb1, hc1, by omega⟩
  · right
    right
    exact ⟨ha1, hb2, hc1, by omega⟩

end Hypertournaments
