import Hypertournaments.OddToggleP3ShiftedAllTrialsCount

/-!
# Shifted RAW source bad patterns equal ordinary bad patterns after XOR

The gauge-correct finite source count uses shifted forbidden
RAW link words. The already certified real endpoint lemma
recognizes ordinary bad-pattern membership of the SHIFTED
mixed word. These two descriptions are exactly equivalent
by the involution of the link-only XOR gauge translation.

We also extract a concrete bad selected trial from the negation
of the all-trials-good event. These deterministic bridges
will be reused for every supported gauge when closing real
non-amalgamation, without assuming any preferred completion.
-/

namespace Hypertournaments

/-- A raw full source word is one of the two gauge-shifted bad
patterns exactly when its XOR-shifted full word is one of the
two ordinary phase-dependent bad patterns. -/
theorem p3ShiftedBadTrialPattern_mem_iff
    (m : ℕ) (shift : Fin m → Bool)
    (choice : Bool → Bool) (w : p3TrialPatternWord m) :
    w ∈ p3ShiftedBadTrialPatternSet m shift choice ↔
      p3ShiftTrialWord m shift w ∈ p3BadTrialPatternSet m choice := by
  classical
  constructor
  · intro hraw
    obtain ⟨phase, _, hphase⟩ := Finset.mem_image.mp hraw
    apply Finset.mem_image.mpr
    refine ⟨phase, Finset.mem_univ _, ?_⟩
    have hh := congrArg (p3ShiftTrialWord m shift) hphase
    change p3ShiftTrialWord m shift
        (p3ShiftTrialWord m shift (p3BadPattern m choice phase)) =
      p3ShiftTrialWord m shift w at hh
    rw [p3ShiftTrialWord_involutive m shift] at hh
    exact hh
  · intro hshifted
    obtain ⟨phase, _, hphase⟩ := Finset.mem_image.mp hshifted
    apply Finset.mem_image.mpr
    refine ⟨phase, Finset.mem_univ _, ?_⟩
    have hh := congrArg (p3ShiftTrialWord m shift) hphase
    change p3ShiftTrialWord m shift
        (p3BadPattern m choice phase) =
      p3ShiftTrialWord m shift
        (p3ShiftTrialWord m shift w) at hh
    rw [p3ShiftTrialWord_involutive m shift] at hh
    exact hh

/-- Not avoiding every shifted bad source word is equivalent to
having a specific selected zero-sum trial whose complete raw
source word is one of the gauge-shifted forbidden patterns. -/
theorem p3NotShiftedGoodSelected_has_bad_trial
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ)
    (shift : p3SelectedTrials G s → Fin (s+1) → Bool)
    (choice : p3SelectedTrials G s → Bool → Bool)
    (words : p3FullSelectedSpace G s → Bool)
    (hbad : words ∉ p3ShiftedGoodSelectedTrialSet s shift choice) :
    ∃ q : p3SelectedTrials G s,
      (fun i : Fin (s+1) ⊕ Unit => words (q,i)) ∈
        p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q) := by
  classical
  by_contra hNo
  have hAll : ∀ q : p3SelectedTrials G s,
      (fun i : Fin (s+1) ⊕ Unit => words (q,i)) ∉
        p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q) := by
    intro q hword
    exact hNo ⟨q,hword⟩
  apply hbad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAll⟩

end Hypertournaments
