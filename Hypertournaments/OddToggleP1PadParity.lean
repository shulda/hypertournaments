import Hypertournaments.OddToggleP1CoreRows
import Hypertournaments.RootedOddFourPadLocalIndex

/-!
# Even row contribution from uniform p1 auxiliary pads

For the n ≡ 1 mod 4 odd-arity exceptional obstruction, the number
of auxiliary pad vertices is m=4k. Each of the six fixed core
vertices receives an even number of positive pad-link entries on
each side.

The right pad-core signs at position s are:
* j=0: s mod 2;
* j=4: 1+s mod 2;
* j in {1,2,3,5}: 1.
The left signs are their complements. This works uniformly for all
k, including the arity-five seed k=0.

These exact arithmetic facts will be combined with the separately
certified finite six-core row parities to prove admissibility of
the one-point sides. The entire side structure is not built here.
-/

namespace Hypertournaments

/-- Right raw link sign from pad p_s to core a_j. The domain
`Fin (2*(2*k))` makes the even alternating count directly available
while being arithmetically equal to `Fin (4*k)`. -/
def p1RightPadCoreBit (k : ℕ)
    (s : Fin (2*(2*k))) (j : Fin 6) : Bool :=
  if j = 0 then decide (s.val % 2 = 1)
  else if j = 4 then decide (s.val % 2 = 0)
  else true

def p1LeftPadCoreBit (k : ℕ)
    (s : Fin (2*(2*k))) (j : Fin 6) : Bool :=
  !(p1RightPadCoreBit k s j)

/-- Every core column of the right pad-link matrix has an even
number of positive entries among all 4k pads. -/
theorem p1RightPadCore_column_even
    (k : ℕ) (j : Fin 6) :
    boolPacketPositiveCount
      (fun s : Fin (2*(2*k)) => p1RightPadCoreBit k s j) % 2 = 0 := by
  by_cases h0 : j = 0
  · subst j
    change boolPacketPositiveCount
      (fun s : Fin (2*(2*k)) => decide (s.val % 2 = 1)) % 2 = 0
    rw [boolPacketPositiveCount_alternating_even (2*k)]
    omega
  · by_cases h4 : j = 4
    · subst j
      change boolPacketPositiveCount
        (fun s : Fin (2*(2*k)) => decide (s.val % 2 = 0)) % 2 = 0
      rw [boolPacketPositiveCount_alternating_even_complement (2*k)]
      omega
    · have heq :
          (fun s : Fin (2*(2*k)) => p1RightPadCoreBit k s j) =
            (fun _ : Fin (2*(2*k)) => true) := by
        funext s
        simp [p1RightPadCoreBit, h0, h4]
      rw [heq]
      simp [boolPacketPositiveCount] <;> omega

/-- Every core column of the *left* pad-link matrix has an even
number of positive entries, by Boolean complementation. -/
theorem p1LeftPadCore_column_even
    (k : ℕ) (j : Fin 6) :
    boolPacketPositiveCount
      (fun s : Fin (2*(2*k)) => p1LeftPadCoreBit k s j) % 2 = 0 := by
  change boolPacketPositiveCount
    (fun s : Fin (2*(2*k)) => !p1RightPadCoreBit k s j) % 2 = 0
  rw [boolPacketPositiveCount_not]
  have hr := p1RightPadCore_column_even k j
  have hb := boolPacketPositiveCount_le
    (fun s : Fin (2*(2*k)) => p1RightPadCoreBit k s j)
  omega

end Hypertournaments
