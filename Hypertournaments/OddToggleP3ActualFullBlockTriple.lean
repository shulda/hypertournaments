import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3ActualProtectedTriple
import Hypertournaments.OddToggleP3ProtectedTriplePositions
import Hypertournaments.OddToggleP3SortedBlockFibers

/-!
# Actual p3 full-block old packet: three protected labels select odd-parity singleton facets

Let U be a genuine old subset of m+1 vertices occupying all m
consecutive old blocks. Pick ANY three consecutive block labels
u,u+1,u+2. The exact one-excess occupancy budget implies the
three fibers together have at most four vertices. Their
canonical increasing packet positions form a monotone label
word, with fiber cardinalities exactly the actual block
occupancies.

The abstract protected-triple parity theorem now yields two
genuinely singleton old vertices on opposite deletion parities,
both belonging to this chosen consecutive protected triple.

This closes the actual OLD-SUBSET geometric calculation for q=m;
transport to one-fresh Hyper packet and actual zero-facet/age
membership are still separate.
-/

namespace Hypertournaments

/-- Any actual full-block old packet with exactly one excess
vertex contains, inside any three consecutive block labels,
two globally singleton vertex positions of opposite parity. -/
theorem p3ActualOneFresh_sorted_protectedTriple_singletons
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t))) (hU : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i)
    (start : ℕ) (hstart : start+2 < m) :
    ∃ x y : Fin (m+1),
      x.val%2 ≠ y.val%2 ∧
      (start ≤ p3BlockNumber t (U.orderEmbOfFin hU x) ∧
        p3BlockNumber t (U.orderEmbOfFin hU x) ≤ start+2) ∧
      (start ≤ p3BlockNumber t (U.orderEmbOfFin hU y) ∧
        p3BlockNumber t (U.orderEmbOfFin hU y) ≤ start+2) ∧
      (∀ z : Fin (m+1),
        p3BlockNumber t (U.orderEmbOfFin hU z) =
          p3BlockNumber t (U.orderEmbOfFin hU x) → z=x) ∧
      (∀ z : Fin (m+1),
        p3BlockNumber t (U.orderEmbOfFin hU z) =
          p3BlockNumber t (U.orderEmbOfFin hU y) → z=y) := by
  classical
  let block : Fin (m+1) → ℕ :=
    fun z => p3BlockNumber t (U.orderEmbOfFin hU z)
  let i : Fin m := ⟨start, by omega⟩
  let j : Fin m := ⟨start+1, by omega⟩
  let l : Fin m := ⟨start+2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change start = start+1 at hv
    omega
  have hil : i ≠ l := by
    intro h
    have hv := congrArg Fin.val h
    change start = start+2 at hv
    omega
  have hjl : j ≠ l := by
    intro h
    have hv := congrArg Fin.val h
    change start+1 = start+2 at hv
    omega
  have hMono : Monotone block :=
    p3SortedOldPacket_block_monotone U hU
  have hA :
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start)).card =
      p3BlockOccupancy m t U i := by
    simpa only [block, i] using
      (p3SortedOldPacket_fiber_card_eq_occupancy
        m t (m+1) U hU i)
  have hB :
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+1)).card =
      p3BlockOccupancy m t U j := by
    simpa only [block, j] using
      (p3SortedOldPacket_fiber_card_eq_occupancy
        m t (m+1) U hU j)
  have hC :
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+2)).card =
      p3BlockOccupancy m t U l := by
    simpa only [block, l] using
      (p3SortedOldPacket_fiber_card_eq_occupancy
        m t (m+1) U hU l)
  have hApos :
      0 < (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start)).card := by
    rw [hA]
    exact hall i
  have hBpos :
      0 < (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+1)).card := by
    rw [hB]
    exact hall j
  have hCpos :
      0 < (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+2)).card := by
    rw [hC]
    exact hall l
  have hBound :
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start)).card +
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+1)).card +
      (Finset.univ.filter
        (fun z : Fin (m+1) => block z = start+2)).card ≤ 4 := by
    rw [hA, hB, hC]
    exact p3ActualOneFresh_three_blocks_le_four
      m t ht U hU hall i j l hij hil hjl
  obtain ⟨x,y,hpar,hlabelX,hlabelY,hSingleX,hSingleY⟩ :=
    p3Monotone_protectedTriple_oppositeParity_singletons
      block hMono start hApos hBpos hCpos hBound
  have hrangeX : start ≤ block x ∧ block x ≤ start+2 := by
    rcases hlabelX with hx | hx | hx <;> omega
  have hrangeY : start ≤ block y ∧ block y ≤ start+2 := by
    rcases hlabelY with hy | hy | hy <;> omega
  exact ⟨x,y,hpar,hrangeX,hrangeY,hSingleX,hSingleY⟩

end Hypertournaments
