import Hypertournaments.OddToggleP3SelectedLinkParityHalf

/-!
# Exact half-count for genuine F₂ sums of selected link-source bits

The prior kernel-certified finite half-event was stated as the
Boolean XOR of one chosen link bit and the parity of all others.
Here we prove this equals the literal ZMod 2 sum of ALL selected
link bits, so the exact half-count applies directly to the F₂
left-plus-right link expression obtained from genuine p3 sides.

No real-side source evaluation or non-amalgamation is claimed.
-/

namespace Hypertournaments

/-- A selected source link sum equals 1 in F₂ exactly when the
chosen-source-bit XOR remaining-link parity is true. -/
theorem p3SelectedLinkSum_one_iff_xor_true
    {B : Type*} [DecidableEq B]
    (m : ℕ) (source : Fin m → B) (chosen : Fin m)
    (bits : B → Bool) :
    ((∑ i : Fin m, p1BitToZMod (bits (source i))) = 1) ↔
      ((bits (source chosen) ^^
        p3OtherSelectedLinkParity m source chosen bits) = true) := by
  classical
  let b : Fin m → ZMod 2 :=
    fun i => p1BitToZMod (bits (source i))
  have hn : chosen ∉
      ((Finset.univ : Finset (Fin m)).erase chosen) := by simp
  have hsplit :
      (∑ i : Fin m, b i) =
      b chosen +
        ∑ i ∈ ((Finset.univ : Finset (Fin m)).erase chosen),
          b i := by
    calc
      (∑ i : Fin m, b i) =
          ∑ i ∈ insert chosen
            ((Finset.univ : Finset (Fin m)).erase chosen),
            b i := by rw [Finset.insert_erase (Finset.mem_univ chosen)]
      _ = b chosen +
          ∑ i ∈ ((Finset.univ : Finset (Fin m)).erase chosen),
            b i := Finset.sum_insert hn
  have hxor :
      p1BitToZMod
        (bits (source chosen) ^^
          p3OtherSelectedLinkParity m source chosen bits) =
      ∑ i : Fin m, b i := by
    unfold p3OtherSelectedLinkParity
    rw [p1BitToZMod_xor, p3BitToZMod_roundtrip]
    exact hsplit.symm
  change (∑ i : Fin m, b i) = 1 ↔
    ((bits (source chosen) ^^
      p3OtherSelectedLinkParity m source chosen bits) = true)
  rw [← hxor]
  cases h : (bits (source chosen) ^^
      p3OtherSelectedLinkParity m source chosen bits) <;>
    simp [p1BitToZMod, h]

/-- For each fixed selected zero-sum transversal, exactly half of
the entire global W/link assignments have odd ZMod 2 sum on ALL
its link coefficients. The base W bit and every other trial's
bits are unconstrained. -/
theorem p3ZeroSumFullSource_fixedTrial_linkSum_half
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (q : p3SelectedTrials G s)
    (chosen : Fin (s+1)) :
    let source : Fin (s+1) → p3FullSourceSpace G s :=
      fun i => p3FullTrialSourceIndex s (q, Sum.inl i)
    2 * Nat.card {bits : p3FullSourceSpace G s → Bool //
      (∑ i : Fin (s+1), p1BitToZMod (bits (source i))) = 1} =
    2 ^ (Fintype.card (p3FullSourceSpace G s)) := by
  classical
  intro source
  let A := {bits : p3FullSourceSpace G s → Bool //
    (∑ i : Fin (s+1), p1BitToZMod (bits (source i))) = 1}
  let B := {bits : p3FullSourceSpace G s → Bool //
    ((bits (source chosen) ^^
      p3OtherSelectedLinkParity (s+1) source chosen bits) = true)}
  let e : A ≃ B := {
    toFun := fun a =>
      ⟨a.1, (p3SelectedLinkSum_one_iff_xor_true
        (s+1) source chosen a.1).mp a.2⟩
    invFun := fun b =>
      ⟨b.1, (p3SelectedLinkSum_one_iff_xor_true
        (s+1) source chosen b.1).mpr b.2⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; cases x; rfl
  }
  have hcard : Nat.card A = Nat.card B := Nat.card_congr e
  change 2 * Nat.card A = 2 ^ (Fintype.card (p3FullSourceSpace G s))
  rw [hcard]
  exact p3ZeroSumFullSource_fixedTrial_linkParity_half s q chosen

end Hypertournaments
