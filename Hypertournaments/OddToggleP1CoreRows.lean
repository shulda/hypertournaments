import Hypertournaments.OddToggleP1Core

/-!
# Exact six-core base packet and link-row parity for the p1 obstruction

The common base has raw facet bits (1,1,0,1,0,1).
The left six-core link matrix has row parities exactly equal to
these base signs. The right link matrix differs in parity only at
the two protected core vertices a0 and a4.

The file checks these data using the actual finite six-vertex
tables, not a free assumption about the source diagram. For
arities 4k+5 the 4k auxiliary pads contribute even row parity;
that separate uniform pad-count calculation is not proved here.
-/

namespace Hypertournaments

/-- The six prescribed raw signs on the common core. -/
def p1CoreBaseBit (j : Fin 6) : Bool :=
  decide (j ≠ 2 ∧ j ≠ 4)

/-- The full symmetric link bit including the diagonal, which is
irrelevant and set to zero. -/
def p1CoreLeftSymBit (i j : Fin 6) : Bool :=
  if i = j then false
  else p1CoreLeftBit (min i j) (max i j)

def p1CoreRightSymBit (i j : Fin 6) : Bool :=
  if i = j then false
  else p1CoreRightBit (min i j) (max i j)

/-- Parity of the six core link edges incident with a given vertex. -/
def p1CoreLinkRowParity
    (link : Fin 6 → Fin 6 → Bool) (j : Fin 6) : ℕ :=
  ((Finset.univ.filter (fun u : Fin 6 => link j u = true)).card) % 2

/-- Left-side row parity is exactly the common base bit for all six
core vertices (the finite part of the side admissibility proof). -/
theorem p1Core_left_row_parity :
    ∀ j : Fin 6,
      p1CoreLinkRowParity p1CoreLeftSymBit j =
        (if p1CoreBaseBit j then 1 else 0) := by
  decide

/-- Right-side row parity differs from the common base at precisely
a0 and a4; these are the two intended homogeneous packets. -/
theorem p1Core_right_row_parity :
    ∀ j : Fin 6,
      p1CoreLinkRowParity p1CoreRightSymBit j =
        ((if p1CoreBaseBit j then 1 else 0) +
         (if j = 0 ∨ j = 4 then 1 else 0)) % 2 := by
  decide

/-- The first forced edge reads raw right-link sign 1 at pair 24. -/
theorem p1Core_forced_pair_24_signs :
    p1CoreLeftBit 2 4 = false ∧
    p1CoreRightBit 2 4 = true := by
  decide

/-- The second forced edge reads raw right-link sign 0 at pair 25. -/
theorem p1Core_forced_pair_25_signs :
    p1CoreLeftBit 2 5 = true ∧
    p1CoreRightBit 2 5 = false := by
  decide

end Hypertournaments
