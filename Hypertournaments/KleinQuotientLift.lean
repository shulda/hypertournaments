import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Ring.Parity

/-!
# Lifting prime-group quotients through prime-to-kernel extensions

A surjective homomorphism onto a `p`-group restricts to a surjection on
every Sylow `p`-subgroup. If the kernel order is prime to `p`, that
restriction is an isomorphism. This includes quotients of order four
with odd kernel and uses only the Sylow image theorem.
-/

namespace Hypertournaments

universe u v

/-- Every Sylow subgroup maps onto a prime-group quotient. -/
theorem sylow_restrict_surjective_of_isPGroup
    {p : ℕ} [Fact p.Prime] {L : Type u} {E : Type v}
    [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r) (hE : IsPGroup p E)
    (P : Sylow p L) : Function.Surjective (r.comp (P : Subgroup L).subtype) := by
  have htop : ((P.mapSurjective hr : Sylow p E) : Subgroup E) = ⊤ :=
    (P.mapSurjective hr).is_maximal' (hE.to_subgroup ⊤) le_top |>.symm
  intro e
  have he : e ∈ (P : Subgroup L).map r := by
    rw [← Sylow.coe_mapSurjective hr P, htop]
    trivial
  obtain ⟨x, hx, he⟩ := he
  exact ⟨⟨x, hx⟩, he⟩

/-- A prime-to-`p` kernel meets a Sylow `p`-subgroup trivially. -/
theorem sylow_inf_ker_eq_bot
    {p : ℕ} [Fact p.Prime] {L : Type u} {E : Type v}
    [Group L] [Group E] [Finite L]
    (r : L →* E) (hker : ¬ p ∣ Nat.card r.ker) (P : Sylow p L) :
    (P : Subgroup L) ⊓ r.ker = ⊥ := by
  let R : Subgroup L := (P : Subgroup L) ⊓ r.ker
  have hp : IsPGroup p R :=
    P.isPGroup'.to_le inf_le_left
  have hnot : ¬ p ∣ Nat.card R :=
    fun h => hker (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  exact R.card_eq_one.mp (hp.card_eq_or_dvd.resolve_right hnot)

/-- The restriction to any Sylow subgroup is injective when the kernel
has order indivisible by the Sylow prime. -/
theorem sylow_restrict_injective_of_prime_not_dvd_ker
    {p : ℕ} [Fact p.Prime] {L : Type u} {E : Type v}
    [Group L] [Group E] [Finite L]
    (r : L →* E) (hker : ¬ p ∣ Nat.card r.ker) (P : Sylow p L) :
    Function.Injective (r.comp (P : Subgroup L).subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  apply Subtype.ext
  have hxmem : (x : L) ∈ (P : Subgroup L) ⊓ r.ker := ⟨x.property, hx⟩
  rw [sylow_inf_ker_eq_bot r hker P] at hxmem
  exact hxmem

/-- A Sylow subgroup is an actual complement for a surjection onto a
`p`-group when the kernel has prime-to-`p` order. -/
noncomputable def sylowQuotientMulEquiv
    {p : ℕ} [Fact p.Prime] {L : Type u} {E : Type v}
    [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r) (hE : IsPGroup p E)
    (hker : ¬ p ∣ Nat.card r.ker) (P : Sylow p L) : P ≃* E :=
  MulEquiv.ofBijective (r.comp (P : Subgroup L).subtype)
    ⟨sylow_restrict_injective_of_prime_not_dvd_ker r hker P,
      sylow_restrict_surjective_of_isPGroup r hr hE P⟩

@[simp] theorem sylowQuotientMulEquiv_apply
    {p : ℕ} [Fact p.Prime] {L : Type u} {E : Type v}
    [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r) (hE : IsPGroup p E)
    (hker : ¬ p ∣ Nat.card r.ker) (P : Sylow p L) (x : P) :
    sylowQuotientMulEquiv r hr hE hker P x = r x := rfl

/-- In the order-four quotient case, every Sylow `2`-subgroup maps
isomorphically onto the quotient if the kernel is odd. -/
noncomputable def kleinQuotientSylowMulEquiv
    {L : Type u} {E : Type v} [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r)
    (hE : Nat.card E = 4) (hker : Odd (Nat.card r.ker))
    (P : Sylow 2 L) : P ≃* E :=
  sylowQuotientMulEquiv r hr (IsPGroup.of_card (p := 2) (n := 2) hE)
    hker.not_two_dvd_nat P

@[simp] theorem kleinQuotientSylowMulEquiv_apply
    {L : Type u} {E : Type v} [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r)
    (hE : Nat.card E = 4) (hker : Odd (Nat.card r.ker))
    (P : Sylow 2 L) (x : P) :
    kleinQuotientSylowMulEquiv r hr hE hker P x = r x := rfl

/-- A concrete subgroup lift of any order-four quotient with odd kernel. -/
theorem exists_klein_quotient_lift
    {L : Type u} {E : Type v} [Group L] [Group E] [Finite L]
    (r : L →* E) (hr : Function.Surjective r)
    (hE : Nat.card E = 4) (hker : Odd (Nat.card r.ker)) :
    ∃ (P : Sylow 2 L) (e : P ≃* E), ∀ x : P, e x = r x := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 L))
  exact ⟨P, kleinQuotientSylowMulEquiv r hr hE hker P, fun _ => rfl⟩

end Hypertournaments
