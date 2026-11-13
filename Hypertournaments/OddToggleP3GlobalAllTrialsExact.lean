import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3FullSourceUniform
import Hypertournaments.OddToggleP3AllTrialsCount
import Hypertournaments.OddToggleP3ZeroSumCount

/-!
# Exact simultaneous finite source-count for all p3 zero-sum trials

This composes the three independently verified counting ingredients:
(1) every selected trial owns its s+1 independent link bits and W bit;
(2) the restriction of global bit assignments to all selected bits
    has exactly uniform finite fibers;
(3) each trial excludes exactly two of the 2^(s+2) possible words,
    uniformly in a phase-dependent forbidden W choice.

The exact number of global W/link assignments avoiding all selected
bad trial patterns is given as an integer ratio, with no probability
measure, event-independence axiom, or hidden product assumption.

The selected trial words here are still abstract Boolean data.
Identifying them with actual forbidden intrinsic mixed packets for
every prospective amalgam is a separate mathematical obligation.
-/

namespace Hypertournaments

/-- The zero-sum code indexes selected independent p3 trials. -/
abbrev p3SelectedTrials (G : Type*) [AddCommGroup G] (s : ℕ) :=
  {q : Fin (s+1) → G // (∑ i : Fin (s+1), q i) = 0}

/-- The good full selected source words: for EVERY trial, its
local (s+1 link bits plus W bit) pattern avoids both forbidden
phase/endpoint patterns, whose choice may depend on the trial. -/
noncomputable def p3GoodSelectedTrialSet
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (choice : p3SelectedTrials G s → Bool → Bool) :
    Finset (p3FullSelectedSpace G s → Bool) := by
  classical
  exact Finset.univ.filter
    (fun bits => ∀ q : p3SelectedTrials G s,
      (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
        p3BadTrialPatternSet (s+1) (choice q))

/-- Exactly (2^(s+2)-2)^|G|^s of the selected bit words avoid
every selected bad mixed-packet pattern. Each trial may have a
different phase-dependent forbidden W choice. -/
theorem p3GoodSelectedTrialSet_card
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (choice : p3SelectedTrials G s → Bool → Bool) :
    (p3GoodSelectedTrialSet s choice).card =
      (2^(s+2)-2)^((Fintype.card G)^s) := by
  classical
  let T := p3SelectedTrials G s
  let GoodBits :=
    {bits : p3FullSelectedSpace G s → Bool //
      ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
        p3BadTrialPatternSet (s+1) (choice q)}
  let GoodFamilies :=
    {family : T → p3TrialPatternWord (s+1) //
      ∀ q : T, family q ∉
        p3BadTrialPatternSet (s+1) (choice q)}
  let equiv : GoodBits ≃ GoodFamilies := {
    toFun := fun bits =>
      ⟨(fun q i => bits.1 (q,i)), (fun q => bits.2 q)⟩
    invFun := fun family =>
      ⟨(fun qi => family.1 qi.1 qi.2), (fun q => family.2 q)⟩
    left_inv := by
      intro bits
      apply Subtype.ext
      funext qi
      rcases qi with ⟨q,i⟩
      rfl
    right_inv := by
      intro family
      apply Subtype.ext
      funext q i
      rfl
  }
  have hSet :
      (p3GoodSelectedTrialSet s choice).card =
        Nat.card GoodBits := by
    classical
    change
      (Finset.univ.filter (fun bits : p3FullSelectedSpace G s → Bool =>
        ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
          p3BadTrialPatternSet (s+1) (choice q))).card =
      Nat.card {bits : p3FullSelectedSpace G s → Bool //
        ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
          p3BadTrialPatternSet (s+1) (choice q)}
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hEquiv : Nat.card GoodBits = Nat.card GoodFamilies :=
    Nat.card_congr equiv
  have hProduct :
      Nat.card GoodFamilies =
        (2^((s+1)+1)-2)^(Fintype.card T) := by
    exact p3GoodTrials_product_card (T:=T)
      (s+1) (by omega) choice
  have hCode : Fintype.card T = (Fintype.card G)^s :=
    p3ZeroSumTuple_card (G:=G) s
  calc
    (p3GoodSelectedTrialSet s choice).card =
        Nat.card GoodBits := hSet
    _ = Nat.card GoodFamilies := hEquiv
    _ = (2^((s+1)+1)-2)^(Fintype.card T) := hProduct
    _ = (2^(s+2)-2)^((Fintype.card G)^s) := by
      have hsum : s+1+1 = s+2 := by omega
      rw [hCode, hsum]

/-- Exact *global* cardinal frequency for simultaneous avoidance
of all selected zero-sum trial patterns, counting every W and link
bit in one genuine finite ambient source space. -/
theorem p3AllGlobalGoodTrialAssignments_exact_ratio
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (choice : p3SelectedTrials G s → Bool → Bool) :
    2^((s+2)*(Fintype.card G)^s) *
      Nat.card {values : p3FullSourceSpace G s → Bool //
        (fun qi : p3FullSelectedSpace G s =>
          values (p3FullTrialSourceIndex s qi)) ∈
          p3GoodSelectedTrialSet s choice} =
      (2^(s+2)-2)^((Fintype.card G)^s) *
        2^(Fintype.card (p3FullSourceSpace G s)) := by
  have h := p3FullTrialRestriction_exact_pattern_ratio
    (G:=G) s (p3GoodSelectedTrialSet s choice)
  rw [p3GoodSelectedTrialSet_card s choice] at h
  exact h

end Hypertournaments
