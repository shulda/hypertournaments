import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Ring.Parity

/-!
# Invariant Sylow subgroups under coprime prime-group actions

An automorphism action of a `q`-group on a finite group whose order is
indivisible by `q` fixes a Sylow `p`-subgroup, for each prime `p`.
The conclusion is stated elementwise, independently of the conjugation
action and pointwise action instances on the type of Sylow subgroups.
-/

namespace Hypertournaments

universe u v

open scoped Pointwise

/-- The number of Sylow subgroups divides the order of a finite group. -/
theorem card_sylow_dvd_card (p : ℕ) [Fact p.Prime]
    (K : Type u) [Group K] [Finite K] :
    Nat.card (Sylow p K) ∣ Nat.card K := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p K))
  exact P.card_dvd_index.trans P.index_dvd_card

/-- Coprime prime-group automorphisms stabilize a Sylow subgroup.
The acting group itself need not be finite. -/
theorem exists_invariant_sylow_of_prime_not_dvd_card
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    {E : Type u} {K : Type v} [Group E] [Group K] [Finite K]
    [MulDistribMulAction E K] (hE : IsPGroup q E)
    (hK : ¬ q ∣ Nat.card K) :
    ∃ P : Sylow p K, ∀ (e : E) (x : K), e • x ∈ P ↔ x ∈ P := by
  let : MulAction E (Sylow p K) := Sylow.pointwiseMulAction
  have hcount : ¬ q ∣ Nat.card (Sylow p K) :=
    fun h => hK (h.trans (card_sylow_dvd_card p K))
  obtain ⟨P, hP⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K) hcount
  refine ⟨P, fun e x => ?_⟩
  have hsub : e • (P : Subgroup K) = (P : Subgroup K) :=
    congrArg Sylow.toSubgroup (hP e)
  change e • x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K)
  simpa only [hsub] using
    (Subgroup.smul_mem_pointwise_smul_iff (a := e) (S := (P : Subgroup K)) (x := x))

/-- In particular, every automorphism action of a `2`-group on an odd-order
finite group stabilizes a Sylow subgroup at every prime. -/
theorem exists_invariant_sylow_of_odd_card
    (p : ℕ) [Fact p.Prime]
    {E : Type u} {K : Type v} [Group E] [Group K] [Finite K]
    [MulDistribMulAction E K] (hE : IsPGroup 2 E) (hK : Odd (Nat.card K)) :
    ∃ P : Sylow p K, ∀ (e : E) (x : K), e • x ∈ P ↔ x ∈ P :=
  exists_invariant_sylow_of_prime_not_dvd_card p 2 hE hK.not_two_dvd_nat

end Hypertournaments
