import Hypertournaments.OddToggleP3ExplicitSideSupport

/-!
# Sparse p3 side packets: two entirely missing old blocks kill every facet

A nonzero base coefficient W must be supported on a full block
transversal. A nonzero one-point link coefficient L/R can miss
exactly one old block. Therefore if a side subset lacks TWO distinct
old block labels, the side potential vanishes there, regardless
of eligible half, and its coboundary vanishes there as well.

This handles the low-occupancy branch (≤m−2 occupied blocks)
of the genuine p3 random-side admissibility argument. It is
independent of random coefficient choices and of protected-half
parity geometry.
-/

namespace Hypertournaments

/-- No nonzero p3 one-point side potential entry can omit two
distinct base block labels simultaneously. -/
theorem p3SidePotential_zero_of_two_missing_blocks
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V)
    (i j : Fin m) (hij : i ≠ j)
    (hmissi : ∀ v : Fin (m*t), old v ∈ Q →
      p3BlockNumber t v ≠ i.val)
    (hmissj : ∀ v : Fin (m*t), old v ∈ Q →
      p3BlockNumber t v ≠ j.val) :
    p3SidePotential m t old fresh eligible W L Q = 0 := by
  classical
  by_contra hnonzero
  let U := p3SideOldPart old Q
  have hsource (b : Fin m)
      (hone : p3BlockOccupancy m t U b = 1) :
      ∃ v : Fin (m*t), old v ∈ Q ∧ p3BlockNumber t v = b.val := by
    obtain ⟨v, hv, hblock⟩ :=
      p3BlockOccupancy_one_witness m t U b hone
    refine ⟨v, ?_, hblock⟩
    simpa [U, p3SideOldPart] using hv
  by_cases hfresh : fresh ∈ Q
  · have hs : p3IsEligibleMissingTransversal m t eligible U := by
      by_contra hn
      have hz : p3SidePotential m t old fresh eligible W L Q = 0 := by
        simp [p3SidePotential, hfresh, hn, U]
      exact hnonzero hz
    obtain ⟨_, missing, _, _, hother⟩ := hs
    have hchoice : i ≠ missing ∨ j ≠ missing := by
      by_cases him : i = missing
      · right
        intro hjm
        exact hij (him.trans hjm.symm)
      · left
        exact him
    rcases hchoice with him | hjm
    · obtain ⟨v,hv,heq⟩ := hsource i (hother i him)
      exact (hmissi v hv) heq
    · obtain ⟨v,hv,heq⟩ := hsource j (hother j hjm)
      exact (hmissj v hv) heq
  · have hs : p3IsBlockTransversal m t U := by
      by_contra hn
      have hz : p3SidePotential m t old fresh eligible W L Q = 0 := by
        simp [p3SidePotential, hfresh, hn, U]
      exact hnonzero hz
    obtain ⟨v,hv,heq⟩ := hsource i (hs.2 i)
    exact (hmissi v hv) heq

/-- Whenever two old blocks are absent from a side subset,
the orientation coboundary of its side potential is zero. -/
theorem p3SidePotential_coboundary_zero_of_two_missing_blocks
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V)
    (i j : Fin m) (hij : i ≠ j)
    (hmissi : ∀ v : Fin (m*t), old v ∈ Q →
      p3BlockNumber t v ≠ i.val)
    (hmissj : ∀ v : Fin (m*t), old v ∈ Q →
      p3BlockNumber t v ≠ j.val) :
    coboundary (p3SidePotential m t old fresh eligible W L) Q = 0 := by
  unfold coboundary
  apply Finset.sum_eq_zero
  intro x hx
  apply p3SidePotential_zero_of_two_missing_blocks
    m t old fresh eligible W L (Q.erase x) i j hij
  · intro v hv
    exact hmissi v (Finset.mem_of_mem_erase hv)
  · intro v hv
    exact hmissj v (Finset.mem_of_mem_erase hv)

end Hypertournaments
