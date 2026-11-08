import Hypertournaments.Basic

/-!
# Finite adjacent-swap tables for six-facet packets

For five-hypertournaments, every local packet has six facets.  We
kernel-check the thirty possible combinations of an adjacent swap of
six coordinates and a deleted coordinate.  This is the arity-five
counterpart of AdjacentPacketFour, independent of any seed tables.
-/

namespace Hypertournaments

/-- Swap adjacent positions p and p+1 of a six-tuple. -/
def adjacentSwap5 (p : Fin 5) : Equiv.Perm (Fin 6) :=
  Equiv.swap p.castSucc p.succ

/-- Permutation induced on the five surviving coordinates when an
adjacent swap is performed on a six-tuple and one coordinate is deleted. -/
def facetSwap5 (p : Fin 5) (k : Fin 6) : Equiv.Perm (Fin 5) :=
  if (p.val = 0 ∧ 2 ≤ k.val) ∨ (p.val = 1 ∧ k.val = 0) then
    Equiv.swap (0 : Fin 5) 1
  else if (p.val = 1 ∧ 3 ≤ k.val) ∨
      (p.val = 2 ∧ k.val ≤ 1) then
    Equiv.swap (1 : Fin 5) 2
  else if (p.val = 2 ∧ 4 ≤ k.val) ∨
      (p.val = 3 ∧ k.val ≤ 2) then
    Equiv.swap (2 : Fin 5) 3
  else if (p.val = 3 ∧ k.val = 5) ∨
      (p.val = 4 ∧ k.val ≤ 3) then
    Equiv.swap (3 : Fin 5) 4
  else
    1

/-- All thirty finite facet-coordinate identities are checked by
reduction; no orientation or class assumption is used. -/
theorem facetSwap5_correct (p : Fin 5) (k : Fin 6) :
    (Fin.succAboveEmb k).trans (adjacentSwap5 p).toEmbedding =
      (facetSwap5 p k).toEmbedding.trans
        (Fin.succAboveEmb ((adjacentSwap5 p) k)) := by
  ext i
  fin_cases p <;> fin_cases k <;> fin_cases i <;> decide

/-- Minority count of the six Boolean normalized facet signs. -/
def minority6 (b : Fin 6 → Bool) : ℕ :=
  let c := (Finset.univ.filter (fun i => b i = true)).card
  min c (6 - c)

/-- A permutation followed by simultaneous complementation preserves
the six-facet minority count. This finite fact is kernel checked. -/
theorem minority6_adjacent_complement :
    ∀ (b : Fin 6 → Bool) (p : Fin 5),
      minority6 (fun i => !(b ((adjacentSwap5 p) i))) =
        minority6 b := by
  unfold minority6 adjacentSwap5
  decide +kernel

end Hypertournaments
