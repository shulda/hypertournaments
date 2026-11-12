import Hypertournaments.OddToggleP3SixBlockGeometry

/-!
# Singleton block fibers at consecutive labels have opposite sorted parity

For an increasing old-vertex packet, block labels are monotone along
sorted vertex positions. If two consecutive block labels occur
exactly once each, their unique vertices occur in consecutive
positions and hence at opposite deletion parities.

This exact finite lemma is independent of the p3 random coefficients
and of how the singleton labels were selected. Together with the
previously certified six-block selection it is the missing
geometric transfer from block occupancies to protected facets.
-/

namespace Hypertournaments

/-- In any monotone finite sequence of natural block labels,
singleton fibers of consecutive labels have positions of opposite
parity, as well as exactly adjacent positions. -/
theorem p3ConsecutiveSingletonFibers_oppositeParity
    (N : ℕ) (block : Fin N → ℕ) (hmono : Monotone block)
    (a : ℕ)
    (hfirst :
      (Finset.univ.filter (fun x : Fin N => block x = a)).card = 1)
    (hsecond :
      (Finset.univ.filter (fun x : Fin N => block x = a+1)).card = 1) :
    ∃ x y : Fin N,
      block x = a ∧ block y = a+1 ∧
      y.val = x.val + 1 ∧
      decide (x.val % 2 = 1) ≠ decide (y.val % 2 = 1) := by
  classical
  obtain ⟨x, hxset⟩ := Finset.card_eq_one.mp hfirst
  obtain ⟨y, hyset⟩ := Finset.card_eq_one.mp hsecond
  have hxmem :
      x ∈ (Finset.univ.filter (fun q : Fin N => block q = a)) := by
    rw [hxset]
    simp
  have hymem :
      y ∈ (Finset.univ.filter (fun q : Fin N => block q = a+1)) := by
    rw [hyset]
    simp
  have hx : block x = a := (Finset.mem_filter.mp hxmem).2
  have hy : block y = a+1 := (Finset.mem_filter.mp hymem).2
  have huniquex (q : Fin N) (hq : block q = a) : q = x := by
    have hmem :
        q ∈ (Finset.univ.filter (fun r : Fin N => block r = a)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    rw [hxset] at hmem
    simpa using hmem
  have huniquey (q : Fin N) (hq : block q = a+1) : q = y := by
    have hmem :
        q ∈ (Finset.univ.filter (fun r : Fin N => block r = a+1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    rw [hyset] at hmem
    simpa using hmem
  have hstep : block y = block x + 1 := by omega
  have hadj : y.val = x.val + 1 :=
    p3Consecutive_singleton_blocks_adjacent_positions
      N block hmono x y hstep
      (by
        intro q hq
        exact huniquex q (hq.trans hx))
      (by
        intro q hq
        exact huniquey q (hq.trans hy))
  have hpar : decide (x.val%2=1) ≠ decide (y.val%2=1) := by
    by_cases hp : x.val%2=1
    · have hq : y.val%2≠1 := by omega
      simp [hp, hq]
    · have hq : y.val%2=1 := by omega
      simp [hp, hq]
  exact ⟨x, y, hx, hy, hadj, hpar⟩

end Hypertournaments
