import Hypertournaments.Basic

/-!
# Adjacent swaps of five-coordinate packets

The action of an adjacent transposition on each of the five
four-dimensional facets is a finite equality of injective coordinate
maps. The induced permutation of the four remaining coordinates is
either the identity or another adjacent swap. This computational
table has only 20 cases and is kernel checked.

Together with the elementary five-bit minority identity, it
provides the finite combinatorial core for proving that the local
arity-four type index is independent of the ordering of vertices.
-/

namespace Hypertournaments

/-- Swap adjacent coordinates p and p+1 of a five-tuple. -/
def adjacentSwap4 (p : Fin 4) : Equiv.Perm (Fin 5) :=
  Equiv.swap p.castSucc p.succ

/-- The induced permutation of the four surviving coordinates after
deleting position k. In each case it is an adjacent swap or identity. -/
def facetSwap4 (p : Fin 4) (k : Fin 5) : Equiv.Perm (Fin 4) :=
  if (p.val = 0 ∧ 2 ≤ k.val) ∨ (p.val = 1 ∧ k.val = 0) then
    Equiv.swap (0 : Fin 4) 1
  else if (p.val = 1 ∧ 3 ≤ k.val) ∨
      (p.val = 2 ∧ k.val ≤ 1) then
    Equiv.swap (1 : Fin 4) 2
  else if (p.val = 2 ∧ k.val = 4) ∨
      (p.val = 3 ∧ k.val ≤ 2) then
    Equiv.swap (2 : Fin 4) 3
  else
    1

/-- All twenty coordinate identities are checked independently
of any particular hyperorientation. -/
theorem facetSwap4_correct (p : Fin 4) (k : Fin 5) :
    (Fin.succAboveEmb k).trans (adjacentSwap4 p).toEmbedding =
      (facetSwap4 p k).toEmbedding.trans
        (Fin.succAboveEmb ((adjacentSwap4 p) k)) := by
  ext i
  fin_cases p <;> fin_cases k <;> fin_cases i <;>
    decide

/-- The minority count of five Boolean signs is unchanged
when all signs are complemented and the positions are swapped. -/
def minority5 (b : Fin 5 → Bool) : ℕ :=
  let c := (Finset.univ.filter (fun i => b i = true)).card
  min c (5 - c)

theorem minority5_adjacent_complement :
    ∀ (b : Fin 5 → Bool) (p : Fin 4),
      minority5 (fun i => !(b ((adjacentSwap4 p) i))) =
        minority5 b := by
  unfold minority5 adjacentSwap4
  decide +kernel

end Hypertournaments
