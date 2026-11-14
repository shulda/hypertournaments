import Hypertournaments.FiveConstrained.CertificatesBasic
import Mathlib.Tactic.Tauto

/-!
# Logical meaning of the finite requirement masks

Every bit is an actual local requirement. These lemmas connect the executable
folds and bitwise tests to universal statements, independently of how any
particular certificate was found.
-/

namespace Hypertournaments.FiveConstrained

@[simp] theorem mem_certificatePairs (n a b : ℕ) :
    (a, b) ∈ certificatePairs n ↔ a < n ∧ b < n ∧ a < b := by
  simp [certificatePairs, and_assoc, and_left_comm, and_comm]

@[simp] theorem mem_certificateTriples (n a b c : ℕ) :
    (a, b, c) ∈ certificateTriples n ↔
      a < n ∧ b < n ∧ c < n ∧ a < b ∧ b < c := by
  simp [certificateTriples, and_assoc, and_left_comm, and_comm]

@[simp] theorem mem_certificateFourSets (n a b c d : ℕ) :
    (a, b, c, d) ∈ certificateFourSets n ↔
      a < n ∧ b < n ∧ c < n ∧ d < n ∧ a < b ∧ b < c ∧ c < d := by
  simp [certificateFourSets, and_assoc, and_left_comm, and_comm]

@[simp] theorem mem_certificateFiveSets (n a b c d e : ℕ) :
    (a, b, c, d, e) ∈ certificateFiveSets n ↔
      a < n ∧ b < n ∧ c < n ∧ d < n ∧ e < n ∧
        a < b ∧ b < c ∧ c < d ∧ d < e := by
  simp [certificateFiveSets, and_assoc, and_left_comm, and_comm]

theorem certificateSubset_iff (required allowed : ℕ) :
    certificateSubset required allowed = true ↔
      ∀ i, required.testBit i = true → allowed.testBit i = true := by
  simp only [certificateSubset, beq_iff_eq]
  constructor
  · intro h i hi
    have hb := congrArg (fun x : ℕ => x.testBit i) h
    simpa only [Nat.testBit_land, hi, Bool.true_and] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    cases hr : required.testBit i
    · rfl
    · simp [h i hr]

theorem certificateSubset_zero (allowed : ℕ) : certificateSubset 0 allowed = true := by
  apply (certificateSubset_iff _ _).mpr
  simp

theorem certificateSubset_addType_iff (mask label allowed : ℕ) :
    certificateSubset (certificateAddType mask label) allowed = true ↔
      certificateSubset mask allowed = true ∧ allowed.testBit label = true := by
  simp only [certificateSubset_iff, certificateAddType, Nat.testBit_lor,
    Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), h label (Or.inr rfl)⟩
  · rintro ⟨h, hl⟩ i (hi | rfl)
    · exact h i hi
    · exact hl

theorem certificateSubset_fold_iff {α : Type*} (xs : List α)
    (label : α → ℕ) (initial allowed : ℕ) :
    certificateSubset (xs.foldl (fun mask x => certificateAddType mask (label x)) initial)
      allowed = true ↔
      certificateSubset initial allowed = true ∧
        ∀ x ∈ xs, allowed.testBit (label x) = true := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, certificateSubset_addType_iff,
      List.mem_cons, forall_eq_or_imp]
    tauto

theorem certificateSubset_fold_zero_iff {α : Type*} (xs : List α)
    (label : α → ℕ) (allowed : ℕ) :
    certificateSubset (xs.foldl (fun mask x => certificateAddType mask (label x)) 0)
      allowed = true ↔ ∀ x ∈ xs, allowed.testBit (label x) = true := by
  rw [certificateSubset_fold_iff]
  simp [certificateSubset_zero]

theorem certificateAccepts_iff (palette : ℕ) (r : CertificateRequirements) :
    certificateAccepts palette r = true ↔
      (∀ i, r.four.testBit i = true → (certificateSupport4 palette).testBit i = true) ∧
      (∀ i, r.five.testBit i = true → palette.testBit i = true) := by
  simp only [certificateAccepts, Bool.and_eq_true, certificateSubset_iff]

theorem certificateBlocks_iff (palette : ℕ) (p : CertificateProfile) :
    certificateBlocks palette p = true ↔
      certificateAccepts palette p.side = true ∧
        ∀ r ∈ p.mixed, certificateAccepts palette r = false := by
  simp [certificateBlocks]

theorem certificateCheck_iff (palette : ℕ) (d : CertificateDiagram) :
    certificateCheck palette d = true ↔
      d.left ≠ d.right ∧ certificateAccepts palette (certificateSideRequirements d) = true ∧
        ∀ x < 2 ^ d.baseSize,
          certificateAccepts palette (certificateMixedRequirements d x) = false := by
  simp [certificateCheck, certificateBlocks_iff, certificateProfile]

private theorem certificateSubset_fold_twice_iff {α β : Type*}
    (xs : List α) (ys : List β) (label : α → β → ℕ) (allowed : ℕ) :
    certificateSubset
      (xs.foldl (fun mask x => ys.foldl
        (fun mask y => certificateAddType mask (label x y)) mask) 0) allowed = true ↔
      ∀ x ∈ xs, ∀ y ∈ ys, allowed.testBit (label x y) = true := by
  suffices ∀ initial, certificateSubset
      (xs.foldl (fun mask x => ys.foldl
        (fun mask y => certificateAddType mask (label x y)) mask) initial) allowed = true ↔
      certificateSubset initial allowed = true ∧
        ∀ x ∈ xs, ∀ y ∈ ys, allowed.testBit (label x y) = true by
    simpa [certificateSubset_zero] using this 0
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro initial
    simp only [List.foldl_cons, ih, certificateSubset_fold_iff,
      List.mem_cons, forall_eq_or_imp]
    tauto

theorem certificateSideRequirements_iff (palette : ℕ) (d : CertificateDiagram) :
    certificateAccepts palette (certificateSideRequirements d) = true ↔
      (∀ rightSide ∈ [false, true], ∀ q ∈ certificateFourSets (d.baseSize + 1),
        (certificateSupport4 palette).testBit (certificateSideType4 d rightSide q) = true) ∧
      (∀ rightSide ∈ [false, true], ∀ q ∈ certificateFiveSets (d.baseSize + 1),
        palette.testBit (type5 (certificateSidePacket5 d rightSide q)).val = true) := by
  simp only [certificateAccepts, Bool.and_eq_true, certificateSideRequirements]
  exact and_congr (certificateSubset_fold_twice_iff _ _ _ _)
    (certificateSubset_fold_twice_iff _ _ _ _)

theorem certificateMixedRequirements_iff (palette : ℕ) (d : CertificateDiagram) (x : ℕ) :
    certificateAccepts palette (certificateMixedRequirements d x) = true ↔
      (∀ q ∈ certificatePairs d.baseSize,
        (certificateSupport4 palette).testBit (certificateMixedType4 d x q.1 q.2) = true) ∧
      (∀ q ∈ certificateTriples d.baseSize,
        palette.testBit (type5 (certificateMixedPacket5 d x q.1 q.2.1 q.2.2)).val = true) := by
  simp only [certificateAccepts, Bool.and_eq_true, certificateMixedRequirements,
    certificateSubset_fold_zero_iff]

end Hypertournaments.FiveConstrained
