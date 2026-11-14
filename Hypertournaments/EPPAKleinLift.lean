import Hypertournaments.EPPAExtension
import Hypertournaments.OddStabilizer
import Hypertournaments.KleinQuotientLift
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega

/-!
# Lifting a local Klein action through separate EPPA extensions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. The subgroup of pairs agreeing on a
packet maps onto the local Klein group. Its kernel embeds in an odd
pointwise stabilizer, so a Sylow subgroup gives an actual homomorphic lift.
-/

namespace Hypertournaments

universe u v w

/-- Pairs of an ambient automorphism and a prescribed packet permutation
which agree on the chosen embedded packet form an actual subgroup. -/
def Hyper.packetExtensionGroup {n : ℕ} {V : Type u} {E : Type v}
    [Group E] (B : Hyper n V) (f : Fin (n + 1) ↪ V)
    (ρ : E →* Equiv.Perm (Fin (n + 1))) : Subgroup (B.Aut × E) where
  carrier := {z | ∀ i, (z.1 : Equiv.Perm V) (f i) = f ((ρ z.2) i)}
  one_mem' := by
    intro i
    simp
  mul_mem' := by
    intro a b ha hb i
    change (a.1 : Equiv.Perm V) ((b.1 : Equiv.Perm V) (f i)) =
      f ((ρ (a.2 * b.2)) i)
    rw [hb i, ha, map_mul]
    rfl
  inv_mem' := by
    intro a ha i
    have h := congrArg (a.1 : Equiv.Perm V).symm (ha ((ρ a.2).symm i))
    change ((a.1 : Equiv.Perm V).symm) (f i) = f ((ρ a.2⁻¹) i)
    rw [map_inv]
    change ((a.1 : Equiv.Perm V).symm) (f i) = f ((ρ a.2).symm i)
    simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h.symm

/-- Separate extensions of a Klein packet action can be chosen homomorphically,
using oddness of the true pointwise stabilizer rather than coherent EPPA. -/
theorem Hyper.lift_packet_perm_action {n : ℕ} {V : Type u} {E : Type v}
    [Finite V] [Group E] [IsKleinFour E]
    (B : Hyper n V) (hn : 2 ≤ n) (f : Fin (n + 1) ↪ V)
    (ρ : E →* Equiv.Perm (Fin (n + 1)))
    (hext : ∀ a : E, ∃ g : B.Aut,
      ∀ i, (g : Equiv.Perm V) (f i) = f ((ρ a) i)) :
    ∃ σ : E →* B.Aut, ∀ a i, (σ a : Equiv.Perm V) (f i) = f ((ρ a) i) := by
  classical
  let : Finite E := IsKleinFour.instFinite
  let L := B.packetExtensionGroup f ρ
  let r : L →* E := (MonoidHom.snd B.Aut E).comp L.subtype
  have hr : Function.Surjective r := by
    intro a
    obtain ⟨g, hg⟩ := hext a
    exact ⟨⟨(g, a), hg⟩, rfl⟩
  let S : Finset V := Finset.univ.image f
  let K := B.pointwiseStabilizer (S : Set V)
  have hS : S.card = n + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hK : Odd (Nat.card K) :=
    B.odd_card_pointwiseStabilizer hn S (by omega)
  let j : r.ker →* K :=
    { toFun := fun z => ⟨z.val.val.1, by
        apply Hyper.mem_pointwiseStabilizer_iff.mpr
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        have hz := z.val.property i
        have hsecond : z.val.val.2 = 1 := z.property
        simpa only [hsecond, map_one, Equiv.Perm.one_apply] using hz⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hxy
    · exact x.property.trans y.property.symm
  have hker : Odd (Nat.card r.ker) :=
    hK.of_dvd_nat (Subgroup.card_dvd_of_injective j hj)
  obtain ⟨P, iso, hiso⟩ := exists_klein_quotient_lift r hr (by simp) hker
  let liftSection : E →* L := (P : Subgroup L).subtype.comp iso.symm.toMonoidHom
  let σ : E →* B.Aut :=
    (MonoidHom.fst B.Aut E).comp (L.subtype.comp liftSection)
  refine ⟨σ, ?_⟩
  intro a i
  have hs : r (liftSection a) = a := by
    change r ((iso.symm a : P) : L) = a
    rw [← hiso]
    exact iso.apply_symm_apply a
  have hh := (liftSection a).property i
  have hsecond : (liftSection a).val.2 = a := hs
  change ((liftSection a).val.1 : Equiv.Perm V) (f i) = f ((ρ a) i)
  simpa only [hsecond] using hh

/-- An ordinary EPPA witness supplies an actual Klein action by ambient
automorphisms extending any local Klein action on an embedded packet. -/
theorem Hyper.IsEPPAWitness.lift_packet_action
    {n : ℕ} {V : Type u} {W : Type v} {E : Type w}
    [Group E] [IsKleinFour E]
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W}
    (h : A.IsEPPAWitness B e) (hn : 2 ≤ n)
    (P : Hyper n (Fin (n + 1))) (f : Fin (n + 1) ↪ V)
    (hf : Preserves P A f) (ρ : E →* P.Aut) :
    ∃ σ : E →* B.Aut, ∀ a i,
      (σ a : Equiv.Perm W) (e (f i)) =
        e (f ((ρ a : Equiv.Perm (Fin (n + 1))) i)) := by
  let : Finite W := h.finite
  let action : E →* Equiv.Perm (Fin (n + 1)) := P.automorphismGroup.subtype.comp ρ
  apply B.lift_packet_perm_action hn (f.trans e) action
  intro a
  let g := (ρ a : Equiv.Perm (Fin (n + 1))).toEmbedding.trans f
  have hg : Preserves P A g := hf.comp (ρ a).preserves
  exact h.extend_isomorphism P f g hf hg

end Hypertournaments
