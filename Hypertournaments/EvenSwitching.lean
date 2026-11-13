import Hypertournaments.HyperCoboundary
import Hypertournaments.OddToggleP1BooleanParity

/-!
# Evenness and the switching palette in every odd arity

An odd-arity packet has even length. Its normalized positive count and
minority index have the same parity. Normalization adds precisely half
the packet length in characteristic two, which is also the central
index appearing in the switching palette. Consequently switching
membership is equivalent to a zero raw facet sum, in both odd congruence
classes modulo four.

All statements use actual injective tuples on an arbitrary carrier;
there is no order, finiteness, or nonemptiness assumption on that carrier.
-/

namespace Hypertournaments

/-- In an odd-arity packet, taking the minority count preserves parity. -/
theorem Hyper.localIndex_mod_two_of_odd {n : ℕ} {V : Type*}
    (A : Hyper n V) (hn : Odd n) (f : Fin (n + 1) ↪ V) :
    localIndex A f % 2 = positiveFacetCount A f % 2 := by
  obtain ⟨k, hk⟩ := hn
  have hcount := positiveFacetCount_le A f
  unfold localIndex
  by_cases hle : positiveFacetCount A f ≤ n + 1 - positiveFacetCount A f
  · rw [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right (le_of_lt (lt_of_not_ge hle))]
    omega

/-- The alternating normalization contributes the central index to raw
facet parity, uniformly across all odd arities. -/
theorem Hyper.normalizedFacetCount_toZMod_of_odd {n : ℕ} {V : Type*}
    (A : Hyper n V) (hn : Odd n) (f : Fin (n + 1) ↪ V) :
    (positiveFacetCount A f : ZMod 2) =
      (boolPacketPositiveCount (fun i => A.orient (facet f i)) : ZMod 2) +
        (centralIndex n : ZMod 2) := by
  let raw : Fin (n + 1) → Bool := fun i => A.orient (facet f i)
  let alt : Fin (n + 1) → Bool := fun i => decide (i.val % 2 = 1)
  have hlen : n + 1 = 2 * centralIndex n := by
    obtain ⟨k, hk⟩ := hn
    unfold centralIndex
    omega
  have hcount : boolPacketPositiveCount alt = centralIndex n := by
    dsimp [alt]
    rw [hlen]
    exact boolPacketPositiveCount_alternating_even (centralIndex n)
  have hxor := p1BoolPacketXor_toZMod raw alt
  rw [hcount] at hxor
  exact hxor

/-- A genuine odd-arity packet belongs to the switching palette exactly
when its raw positive-facet count is even. -/
theorem Hyper.switchingAllowed_iff_rawFacetParity_zero {n : ℕ} {V : Type*}
    (A : Hyper n V) (hn : Odd n) (f : Fin (n + 1) ↪ V) :
    localIndex A f ∈ switchingAllowed n ↔
      (boolPacketPositiveCount (fun i => A.orient (facet f i)) : ZMod 2) = 0 := by
  have hbound := localIndex_le_central A f
  change (localIndex A f ≤ centralIndex n ∧
      localIndex A f % 2 = centralIndex n % 2) ↔ _
  rw [and_iff_right hbound, A.localIndex_mod_two_of_odd hn f,
    ← ZMod.natCast_eq_natCast_iff', A.normalizedFacetCount_toZMod_of_odd hn f]
  constructor
  · intro h
    exact add_right_cancel (h.trans (zero_add _).symm)
  · intro h
    rw [h, zero_add]

/-- Switching membership is precisely vanishing of the intrinsic
unsigned raw facet coboundary, including packets in arity one. -/
theorem Hyper.switchingAllowed_iff_tupleCoboundary_zero {n : ℕ} {V : Type*}
    (A : Hyper n V) (hn : Odd n) (f : Fin (n + 1) ↪ V) :
    localIndex A f ∈ switchingAllowed n ↔
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f = 0 := by
  rw [A.switchingAllowed_iff_rawFacetParity_zero hn f,
    p1BoolPacketPositiveCount_toZMod]
  rfl

/-- In every odd arity, the intrinsic even hypertournaments are exactly
those whose local packets lie in the shared switching palette. -/
theorem Hyper.admissible_switching_iff_isEven {n : ℕ} {V : Type*}
    (A : Hyper n V) (hn : Odd n) :
    Admissible (switchingAllowed n) A ↔ A.IsEven := by
  exact forall_congr' (A.switchingAllowed_iff_tupleCoboundary_zero hn)

end Hypertournaments
