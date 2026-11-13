import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3RealTwoSideLinkParity
import Hypertournaments.OddToggleP3SelectedLinkSumHalf

/-!
# Half-sized genuine endpoint mismatch event in the p3 source space

For any selected real zero-sum transversal, the two actual
canonical one-fresh side orientations with complementary eligible
halves differ exactly when the F₂ sum of all selected global link
source bits is one. The certified finite half-event applies
without inventing independent synthetic orientations.

A separate elementary lemma converts a difference between
canonical sign tables to disagreement on an actual injective
oriented tuple. This is the intrinsic obstruction to identifying
the two fresh vertices in ordinary amalgamation.

The final all-gauge probabilistic non-amalgamation remains open.
-/

namespace Hypertournaments

/-- Any differing canonical sign-table entries on a genuine
n-element set witness disagreement on an actual injective
n-tuple, as required in ordinary one-point non-AP. -/
theorem Hyper.orient_disagree_of_canonicalSignTable_disagree
    {n a : ℕ} (L R : Hyper n (Fin a))
    (Q : Finset (Fin a)) (hQ : Q.card = n)
    (hneq : L.canonicalSignTable Q ≠ R.canonicalSignTable Q) :
    ∃ t : Fin n ↪ Fin a, L.orient t ≠ R.orient t := by
  refine ⟨(Q.orderEmbOfFin hQ).toEmbedding, ?_⟩
  intro heq
  apply hneq
  rw [Hyper.canonicalSignTable_at L Q hQ,
      Hyper.canonicalSignTable_at R Q hQ]
  exact heq

/-- For every fixed genuine selected zero-sum old transversal,
EXACTLY HALF of all global independent source assignments make
the two complementary canonical side endpoint signs different.
The event is formulated on actual intrinsic sides, not on a
synthetic Boolean packet. -/
theorem p3RealSelectedCanonicalLinks_mismatch_half
    (s t : ℕ) [NeZero t] (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (q : p3SelectedTrials (ZMod t) s)
    (chosen : Fin (s+1)) :
    2 * Nat.card {bits : p3FullSourceSpace (ZMod t) s → Bool //
      p3RealSelectedCanonicalLink s t ht eligible bits q ≠
      p3RealSelectedCanonicalLink s t ht
        (Finset.univ \ eligible) bits q} =
    2 ^ (Fintype.card (p3FullSourceSpace (ZMod t) s)) := by
  classical
  let Source := p3FullSourceSpace (ZMod t) s
  let left : (Source → Bool) → ZMod 2 :=
    fun bits => p3RealSelectedCanonicalLink s t ht eligible bits q
  let right : (Source → Bool) → ZMod 2 :=
    fun bits => p3RealSelectedCanonicalLink s t ht
      (Finset.univ \ eligible) bits q
  let sumBits : (Source → Bool) → ZMod 2 :=
    fun bits =>
      ∑ i : Fin (s+1),
        p1BitToZMod (bits (p3FullTrialSourceIndex s (q, Sum.inl i)))
  have hf2 : ∀ x y : ZMod 2, (x ≠ y) ↔ x + y = 1 := by decide
  have hevent (bits : Source → Bool) :
      left bits ≠ right bits ↔ sumBits bits = 1 := by
    have hreal := p3RealSelectedCanonicalLinks_sum_eq_allLinkSources
      s t ht eligible bits q
    change left bits + right bits = sumBits bits at hreal
    simpa only [hreal] using (hf2 (left bits) (right bits))
  let A := {bits : Source → Bool // left bits ≠ right bits}
  let B := {bits : Source → Bool // sumBits bits = 1}
  let equiv : A ≃ B := {
    toFun := fun bits => ⟨bits.1, (hevent bits.1).mp bits.2⟩
    invFun := fun bits => ⟨bits.1, (hevent bits.1).mpr bits.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rfl
    right_inv := by
      intro x
      apply Subtype.ext
      rfl
  }
  have hcard : Nat.card A = Nat.card B := Nat.card_congr equiv
  have hhalf := p3ZeroSumFullSource_fixedTrial_linkSum_half s q chosen
  change 2 * Nat.card B = 2 ^ (Fintype.card Source) at hhalf
  change 2 * Nat.card A = 2 ^ (Fintype.card Source)
  rw [hcard]
  exact hhalf

end Hypertournaments
