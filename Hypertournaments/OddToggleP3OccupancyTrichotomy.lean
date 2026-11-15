import Hypertournaments.OddToggleP3ActualOccupancies

/-!
# Exhaustive block occupancy trichotomy for genuine p3 side packets

For any finite family of old blocks, exactly the following
exhaustive alternatives suffice to check one-fresh side age:
  (1) all old block labels are occupied;
  (2) one chosen old block label is missing and all others occupied;
  (3) two distinct old block labels are both missing.

In the third case, the previously certified genuine side potential
has all orientation facets zero regardless of W,L. In the second
case, the complete q=m-1 age theorem is already kernel-checked.
In the first case, the q=m protected-triple theorem is pending.
This lemma supplies the uniform logical case split, not a
substitute for the actual packet admissibility arguments.
-/

namespace Hypertournaments

/-- A finite indexed family of propositions either holds everywhere,
has exactly one failing index, or has two distinct failing indices. -/
theorem p3FiniteFamily_occupancy_trichotomy
    {I : Type*} (occupied : I → Prop) :
    (∀ i : I, occupied i) ∨
    (∃ missing : I, ¬ occupied missing ∧
      ∀ i : I, i ≠ missing → occupied i) ∨
    (∃ i j : I, i ≠ j ∧ ¬ occupied i ∧ ¬ occupied j) := by
  classical
  by_cases hAll : ∀ i : I, occupied i
  · exact Or.inl hAll
  · obtain ⟨missing, hMissing⟩ :=
      Classical.not_forall.mp hAll
    by_cases hRest : ∀ i : I, i ≠ missing → occupied i
    · exact Or.inr (Or.inl ⟨missing, hMissing, hRest⟩)
    · obtain ⟨j, hJ⟩ := Classical.not_forall.mp hRest
      have hjne : j ≠ missing := by
        intro heq
        apply hJ
        intro h
        exact False.elim (h heq)
      have hjMissing : ¬ occupied j := by
        intro hj
        exact hJ (fun _ => hj)
      exact Or.inr (Or.inr ⟨missing, j, hjne.symm,
        hMissing, hjMissing⟩)

/-- The trichotomy for real finite-set block fibers in the
consecutive-block p3 old base: all occupied, one missing, or at
least two distinct missing blocks. -/
theorem p3ActualPacket_block_occupancy_trichotomy
    (m t : ℕ) (U : Finset (Fin (m*t))) :
    (∀ i : Fin m, 0 < p3BlockOccupancy m t U i) ∨
    (∃ missing : Fin m,
      p3BlockOccupancy m t U missing = 0 ∧
      ∀ i : Fin m, i ≠ missing →
        0 < p3BlockOccupancy m t U i) ∨
    (∃ i j : Fin m,
      i ≠ j ∧ p3BlockOccupancy m t U i = 0 ∧
        p3BlockOccupancy m t U j = 0) := by
  classical
  rcases p3FiniteFamily_occupancy_trichotomy
      (fun i : Fin m => 0 < p3BlockOccupancy m t U i) with
    hAll | ⟨missing, hMissing, hRest⟩ |
      ⟨i, j, hij, hi, hj⟩
  · exact Or.inl hAll
  · exact Or.inr (Or.inl ⟨missing, Nat.eq_zero_of_not_pos hMissing,
      hRest⟩)
  · exact Or.inr (Or.inr ⟨i, j, hij,
      Nat.eq_zero_of_not_pos hi, Nat.eq_zero_of_not_pos hj⟩)

end Hypertournaments
