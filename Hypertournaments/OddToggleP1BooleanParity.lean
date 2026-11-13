import Hypertournaments.TwoPadPacketCount
import Hypertournaments.EvenAlternatingBalance
import Hypertournaments.Cochain

/-!
# Boolean packet XOR as addition in ZMod 2

The p1 exceptional class proof identifies the homogeneous packet
indicator with the raw facet orientation parity. This elementary
bridge evaluates XOR-normalized Boolean facet counts in ZMod 2,
uniformly in packet length. A subsequent lemma can use the known
alternating half-length count to specialize to n ≡ 1 (mod 4).

No hypertournament AP statement or hidden geometric identification
is assumed here.
-/

namespace Hypertournaments

/-- A Boolean bit interpreted as its F₂ value. -/
def p1BitToZMod (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- Exclusive-or is addition over the two-element field. -/
theorem p1BitToZMod_xor (b c : Bool) :
    p1BitToZMod (b ^^ c) = p1BitToZMod b + p1BitToZMod c := by
  cases b <;> cases c <;> decide

/-- The existing finite positive-bit count, cast to F₂, is the
sum of the F₂ indicators of the same Boolean packet. -/
theorem p1BoolPacketPositiveCount_toZMod
    {m : ℕ} (bits : Fin m → Bool) :
    ((boolPacketPositiveCount bits : ℕ) : ZMod 2) =
      ∑ i : Fin m, p1BitToZMod (bits i) := by
  rw [boolPacketPositiveCount_eq_sum]
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : bits i <;> simp [p1BitToZMod, hb]

/-- Taking coordinatewise Boolean XOR adds the two total packet
parities, even though it need not add their ordinary bit counts. -/
theorem p1BoolPacketXor_toZMod
    {m : ℕ} (a b : Fin m → Bool) :
    ((boolPacketPositiveCount (fun i => a i ^^ b i) : ℕ) : ZMod 2) =
      ((boolPacketPositiveCount a : ℕ) : ZMod 2) +
      ((boolPacketPositiveCount b : ℕ) : ZMod 2) := by
  calc
    ((boolPacketPositiveCount (fun i => a i ^^ b i) : ℕ) : ZMod 2) =
        ∑ i : Fin m, p1BitToZMod (a i ^^ b i) :=
      p1BoolPacketPositiveCount_toZMod _
    _ = ∑ i : Fin m,
          (p1BitToZMod (a i) + p1BitToZMod (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact p1BitToZMod_xor (a i) (b i)
    _ = (∑ i : Fin m, p1BitToZMod (a i)) +
          (∑ i : Fin m, p1BitToZMod (b i)) := by
      rw [Finset.sum_add_distrib]
    _ = ((boolPacketPositiveCount a : ℕ) : ZMod 2) +
          ((boolPacketPositiveCount b : ℕ) : ZMod 2) := by
      rw [p1BoolPacketPositiveCount_toZMod,
          p1BoolPacketPositiveCount_toZMod]

end Hypertournaments
