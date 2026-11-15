import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3ShiftedBadTrialPatterns
import Hypertournaments.OddToggleP3GlobalAllTrialsExact

/-!
# Exact simultaneous count of arbitrary gauge-shifted forbidden trials

For each zero-sum trial q, prescribe an arbitrary Boolean link
shift shift(q) and an arbitrary phase-dependent bad W choice(q).
The two forbidden RAW source words have interior
  alternating(phase) XOR shift(q)
and the prescribed W bit. By the preceding local lemma, EXACTLY
two of the 2^(m+1) complete words are excluded for every q.

The selected global source words have disjoint independent
coordinates. Hence the number of all-trial-good selected words
is exactly (2^(m+1)-2)^|G|^(m-1), and the same exact
denominator-free frequency equation holds in the full global
W/link Boolean assignment space. This fixes the missing gauge
shift in the earlier unshifted all-gauge witness.
-/

namespace Hypertournaments

/-- The shifted-good full-trial product is equivalent to a
dependent product of the locally shifted-good word subtypes. -/
def p3ShiftedGoodTrialProductEquiv
    {T : Type*} [Fintype T] (m : ℕ)
    (shift : T → Fin m → Bool)
    (choice : T → Bool → Bool) :
    {family : T → p3TrialPatternWord m //
      ∀ t : T, family t ∉
        p3ShiftedBadTrialPatternSet m (shift t) (choice t)} ≃
    ((t : T) →
      {word : p3TrialPatternWord m //
        word ∉ p3ShiftedBadTrialPatternSet m (shift t) (choice t)}) where
  toFun family t := ⟨family.1 t, family.2 t⟩
  invFun words := ⟨(fun t => (words t).1), (fun t => (words t).2)⟩
  left_inv family := by cases family; rfl
  right_inv words := by
    funext t
    apply Subtype.ext
    rfl

/-- Exact product count for shifted-good trial families. -/
theorem p3ShiftedGoodTrials_product_card
    {T : Type*} [Fintype T] (m : ℕ) (hm : 0 < m)
    (shift : T → Fin m → Bool)
    (choice : T → Bool → Bool) :
    Nat.card
      {family : T → p3TrialPatternWord m //
        ∀ t : T, family t ∉
          p3ShiftedBadTrialPatternSet m (shift t) (choice t)} =
      (2^(m+1)-2)^(Fintype.card T) := by
  classical
  calc
    Nat.card
        {family : T → p3TrialPatternWord m //
          ∀ t : T, family t ∉
            p3ShiftedBadTrialPatternSet m (shift t) (choice t)} =
      Nat.card ((t : T) →
        {word : p3TrialPatternWord m //
          word ∉ p3ShiftedBadTrialPatternSet m (shift t) (choice t)}) :=
        Nat.card_congr (p3ShiftedGoodTrialProductEquiv m shift choice)
    _ = Fintype.card ((t : T) →
        {word : p3TrialPatternWord m //
          word ∉ p3ShiftedBadTrialPatternSet m (shift t) (choice t)}) := by
          simp only [Nat.card_eq_fintype_card]
    _ = ∏ t : T, Fintype.card
        {word : p3TrialPatternWord m //
          word ∉ p3ShiftedBadTrialPatternSet m (shift t) (choice t)} := by
          exact Fintype.card_pi
    _ = ∏ _t : T, (2^(m+1)-2) := by
          apply Finset.prod_congr rfl
          intro t _
          exact p3ShiftedGoodTrialPatterns_card m hm (shift t) (choice t)
    _ = (2^(m+1)-2)^(Fintype.card T) := by simp

/-- The selected global W/link words which avoid both forbidden
SHIFTED RAW source patterns on every selected zero-sum trial. -/
noncomputable def p3ShiftedGoodSelectedTrialSet
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ)
    (shift : p3SelectedTrials G s → Fin (s+1) → Bool)
    (choice : p3SelectedTrials G s → Bool → Bool) :
    Finset (p3FullSelectedSpace G s → Bool) := by
  classical
  exact Finset.univ.filter
    (fun bits => ∀ q : p3SelectedTrials G s,
      (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
        p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q))

/-- Exact selected word count for arbitrary per-trial gauge
shifts, uniform in both shifts and forbidden W choices. -/
theorem p3ShiftedGoodSelectedTrialSet_card
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ)
    (shift : p3SelectedTrials G s → Fin (s+1) → Bool)
    (choice : p3SelectedTrials G s → Bool → Bool) :
    (p3ShiftedGoodSelectedTrialSet s shift choice).card =
      (2^(s+2)-2)^((Fintype.card G)^s) := by
  classical
  let T := p3SelectedTrials G s
  let GoodBits :=
    {bits : p3FullSelectedSpace G s → Bool //
      ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
        p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q)}
  let GoodFamilies :=
    {family : T → p3TrialPatternWord (s+1) //
      ∀ q : T, family q ∉
        p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q)}
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
      (p3ShiftedGoodSelectedTrialSet s shift choice).card =
        Nat.card GoodBits := by
    change
      (Finset.univ.filter
        (fun bits : p3FullSelectedSpace G s → Bool =>
          ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
            p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q))).card =
      Nat.card {bits : p3FullSelectedSpace G s → Bool //
        ∀ q : T, (fun i : Fin (s+1) ⊕ Unit => bits (q,i)) ∉
          p3ShiftedBadTrialPatternSet (s+1) (shift q) (choice q)}
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hEquiv : Nat.card GoodBits = Nat.card GoodFamilies :=
    Nat.card_congr equiv
  have hProduct :
      Nat.card GoodFamilies =
        (2^((s+1)+1)-2)^(Fintype.card T) :=
    p3ShiftedGoodTrials_product_card
      (T:=T) (s+1) (by omega) shift choice
  have hCode : Fintype.card T = (Fintype.card G)^s :=
    p3ZeroSumTuple_card (G:=G) s
  calc
    (p3ShiftedGoodSelectedTrialSet s shift choice).card =
        Nat.card GoodBits := hSet
    _ = Nat.card GoodFamilies := hEquiv
    _ = (2^((s+1)+1)-2)^(Fintype.card T) := hProduct
    _ = (2^(s+2)-2)^((Fintype.card G)^s) := by
      have hh : s+1+1 = s+2 := by omega
      rw [hCode, hh]

/-- Exact denominator-free full global W/link source frequency
for any per-trial Boolean interior gauge shift and bad-W choice. -/
theorem p3ShiftedAllGlobalGoodTrialAssignments_exact_ratio
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ)
    (shift : p3SelectedTrials G s → Fin (s+1) → Bool)
    (choice : p3SelectedTrials G s → Bool → Bool) :
    2^((s+2)*(Fintype.card G)^s) *
      Nat.card {values : p3FullSourceSpace G s → Bool //
        (fun qi : p3FullSelectedSpace G s =>
          values (p3FullTrialSourceIndex s qi)) ∈
          p3ShiftedGoodSelectedTrialSet s shift choice} =
    (2^(s+2)-2)^((Fintype.card G)^s) *
      2^(Fintype.card (p3FullSourceSpace G s)) := by
  have h := p3FullTrialRestriction_exact_pattern_ratio
    (G:=G) s (p3ShiftedGoodSelectedTrialSet s shift choice)
  rw [p3ShiftedGoodSelectedTrialSet_card s shift choice] at h
  exact h

end Hypertournaments
