import Hypertournaments.OddToggleP3BoolPhases
import Hypertournaments.EvenAlternatingBalance
import Hypertournaments.OddToggleP1BooleanParity

/-!
# A p3 alternating mixed interior has ODD F₂ parity

For the exceptional arity n=4k+3 the mixed part of an
(n+1)-packet has m=n-1=4k+2 old-deletion facets. Either
alternating Boolean word of this even length has exactly
m/2=2k+1 positive bits, independent of the initial phase.
Since this is odd, its full F₂ sum is 1.

This exact parity fact is the remaining endpoint compatibility
input: switching parity for an actual parent packet then forces
its last endpoint to be the complement of the other endpoint
once the interior alternates. No probabilistic assumptions.
-/

namespace Hypertournaments

/-- Complementing every Boolean entry exchanges the positive
and negative counts of an m-element packet. -/
theorem p3BoolPacketPositiveCount_not
    {m : ℕ} (bits : Fin m → Bool) :
    boolPacketPositiveCount (fun i => !(bits i)) +
      boolPacketPositiveCount bits = m := by
  classical
  calc
    boolPacketPositiveCount (fun i => !(bits i)) +
        boolPacketPositiveCount bits =
      ∑ i : Fin m,
        ((if !(bits i) then (1:ℕ) else 0) +
         (if bits i then (1:ℕ) else 0)) := by
        rw [boolPacketPositiveCount_eq_sum,
          boolPacketPositiveCount_eq_sum, Finset.sum_add_distrib]
    _ = ∑ _i : Fin m, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        cases h : bits i <;> simp [h]
    _ = m := by simp

/-- Both phases of an actual p3 alternating mixed interior
of length 4k+2 have exactly 2k+1 positive Boolean signs. -/
theorem p3AlternatingInterior_positiveCount
    (k : ℕ) (phase : Bool) :
    boolPacketPositiveCount
      (p3AlternatingWord (4*k+2) phase) = 2*k+1 := by
  let bits : Fin (4*k+2) → Bool := fun i => decide (i.val%2=1)
  have hbase : boolPacketPositiveCount bits = 2*k+1 := by
    dsimp [bits]
    have hlen : 4*k+2 = 2*(2*k+1) := by omega
    rw [hlen]
    exact boolPacketPositiveCount_alternating_even (2*k+1)
  cases phase with
  | false =>
      have hword : p3AlternatingWord (4*k+2) false = bits := by
        funext i
        by_cases he : i.val%2=0
        · have ho : i.val%2≠1 := by omega
          simp [p3AlternatingWord, bits, he,ho]
        · have ho : i.val%2=1 := by omega
          simp [p3AlternatingWord, bits, he,ho]
      rw [hword]
      exact hbase
  | true =>
      have hword :
          p3AlternatingWord (4*k+2) true =
            (fun i : Fin (4*k+2) => !(bits i)) := by
        funext i
        by_cases he : i.val%2=0
        · have ho : i.val%2≠1 := by omega
          simp [p3AlternatingWord,bits,he,ho]
        · have ho : i.val%2=1 := by omega
          simp [p3AlternatingWord,bits,he,ho]
      rw [hword]
      have hcomp := p3BoolPacketPositiveCount_not bits
      omega

/-- The F₂ sum of the true mixed interior facets is 1
whenever their Boolean signs form either alternating word. -/
theorem p3AlternatingInterior_ZModSum_one
    (k : ℕ) (phase : Bool) :
    (∑ i : Fin (4*k+2),
      p1BitToZMod (p3AlternatingWord (4*k+2) phase i)) =
      (1 : ZMod 2) := by
  have hc := p3AlternatingInterior_positiveCount k phase
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hn : (((2*k+1:ℕ) : ZMod 2)) = 1 := by
    calc
      (((2*k+1:ℕ) : ZMod 2)) =
        (2 : ZMod 2)*(k : ZMod 2)+1 := by push_cast; ring
      _ = 1 := by rw [htwo]; simp
  calc
    (∑ i : Fin (4*k+2),
      p1BitToZMod (p3AlternatingWord (4*k+2) phase i)) =
        ((boolPacketPositiveCount
          (p3AlternatingWord (4*k+2) phase) : ℕ) : ZMod 2) :=
        (p1BoolPacketPositiveCount_toZMod _).symm
    _ = ((2*k+1:ℕ) : ZMod 2) := by rw [hc]
    _ = 1 := hn

end Hypertournaments
