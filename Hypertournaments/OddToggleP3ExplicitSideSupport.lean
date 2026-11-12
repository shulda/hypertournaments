import Hypertournaments.OddToggleP3ExplicitPotentials
import Hypertournaments.CanonicalPacket

/-!
# Explicit p3 random-side potentials cover their protected half blocks

The base potential is supported on full m-block transversals.
One-point side-link potential values are supported only on transversals
missing exactly one ELIGIBLE block. When a protected family of block
indices is disjoint from the eligible missing indices, every nonzero
potential on that side uses at least one old vertex from EVERY
protected block.

Consequently deleting the unique vertex of a protected block from
a finite packet makes the actual potential-induced raw facet sign
equal to zero, uniformly in the arbitrary coefficients W,L.

This is the concrete source-support half of the p3 side-age proof.
The separate geometric problem of finding two such zero facets of
opposite parity in EVERY packet is not solved here.
-/

namespace Hypertournaments

/-- A block of occupancy exactly one has a selected old vertex. -/
theorem p3BlockOccupancy_one_witness
    (m t : ℕ) (U : Finset (Fin (m*t))) (i : Fin m)
    (h : p3BlockOccupancy m t U i = 1) :
    ∃ v : Fin (m*t), v ∈ U ∧ p3BlockNumber t v = i.val := by
  have hpos :
      0 < (U.filter (fun v => p3BlockNumber t v = i.val)).card := by
    simpa [p3BlockOccupancy] using (show 0 < 1 by omega : Nat.lt (0:ℕ) 1)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩

/-- Nonzero potential coefficient on a genuine one-point side
contains an old vertex from every protected block. -/
theorem p3SidePotential_nonzero_covers_protected
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible protectedBlocks : Finset (Fin m))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V)
    (hQ : p3SidePotential m t old fresh eligible W L Q ≠ 0)
    (i : Fin m) (hi : i ∈ protectedBlocks) :
    ∃ v : Fin (m*t), old v ∈ Q ∧ p3BlockNumber t v = i.val := by
  classical
  let U := p3SideOldPart old Q
  have hsource (i : Fin m)
      (hone : p3BlockOccupancy m t U i = 1) :
      ∃ v : Fin (m*t), old v ∈ Q ∧ p3BlockNumber t v = i.val := by
    obtain ⟨v, hv, hval⟩ := p3BlockOccupancy_one_witness m t U i hone
    refine ⟨v, ?_, hval⟩
    simpa [U, p3SideOldPart] using hv
  by_cases hnew : fresh ∈ Q
  · have hsupport : p3IsEligibleMissingTransversal m t eligible U := by
      by_contra hn
      have hz : p3SidePotential m t old fresh eligible W L Q = 0 := by
        simp [p3SidePotential, hnew, hn, U]
      exact hQ hz
    obtain ⟨_, missing, hmissEligible, _, hother⟩ := hsupport
    have hneq : i ≠ missing := by
      intro heq
      have hmem : missing ∈ protectedBlocks := by simpa [heq] using hi
      exact (Finset.disjoint_left.mp hdisjoint hmissEligible) hmem
    exact hsource i (hother i hneq)
  · have hsupport : p3IsBlockTransversal m t U := by
      by_contra hn
      have hz : p3SidePotential m t old fresh eligible W L Q = 0 := by
        simp [p3SidePotential, hnew, hn, U]
      exact hQ hz
    exact hsource i (hsupport.2 i)

/-- If a finite side subset omits a protected block entirely, its
potential coboundary vanishes: every potential face misses the block. -/
theorem p3SidePotential_coboundary_zero_of_missing_protected
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible protectedBlocks : Finset (Fin m))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V)
    (i : Fin m) (hi : i ∈ protectedBlocks)
    (hmissing : ∀ v : Fin (m*t), old v ∈ Q →
      p3BlockNumber t v ≠ i.val) :
    coboundary (p3SidePotential m t old fresh eligible W L) Q = 0 := by
  unfold coboundary
  apply Finset.sum_eq_zero
  intro x hx
  by_contra hnonzero
  obtain ⟨v, hv, hblock⟩ :=
    p3SidePotential_nonzero_covers_protected
      m t old fresh eligible protectedBlocks hdisjoint W L
      (Q.erase x) hnonzero i hi
  exact (hmissing v (Finset.mem_of_mem_erase hv)) hblock

/-- Deleting the unique old vertex of a protected block forces
the potential coboundary to vanish on that deleted facet. -/
theorem p3SidePotential_coboundary_zero_of_unique_protected
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible protectedBlocks : Finset (Fin m))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V) (v : Fin (m*t))
    (hprotected : (⟨p3BlockNumber t v, by
      have hpos : 0 < t := by omega
      have hv := v.isLt
      apply (Nat.div_lt_iff_lt_mul hpos).2
      simpa [Nat.mul_comm] using hv⟩ : Fin m) ∈ protectedBlocks)
    (hunique : ∀ w : Fin (m*t), old w ∈ Q →
      p3BlockNumber t w = p3BlockNumber t v → w = v) :
    coboundary (p3SidePotential m t old fresh eligible W L)
      (Q.erase (old v)) = 0 := by
  let i : Fin m := ⟨p3BlockNumber t v, by
    have hpos : 0 < t := by omega
    have hv := v.isLt
    apply (Nat.div_lt_iff_lt_mul hpos).2
    simpa [Nat.mul_comm] using hv⟩
  apply p3SidePotential_coboundary_zero_of_missing_protected
      m t old fresh eligible protectedBlocks hdisjoint W L
      (Q.erase (old v)) i hprotected
  intro w hw hblock
  have hne : old w ≠ old v := (Finset.mem_erase.mp hw).1
  have hsame : w = v :=
    hunique w (Finset.mem_of_mem_erase hw) hblock
  exact hne (congrArg old hsame)

end Hypertournaments
