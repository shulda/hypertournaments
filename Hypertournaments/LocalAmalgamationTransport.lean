import Hypertournaments.LocalForbiddenFamily
import Hypertournaments.FiniteStrongSpan
import Hypertournaments.Amalgamation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ext

/-!
# Transport between local palettes and actual amalgamation interfaces

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:constrained-classification`. Only realized local indices matter.
The finite-presentation transport keeps the exact overlap of the original
carrier, and does not impose an order on the source embeddings.
-/

namespace Hypertournaments

/-- Agreement at every possible local index gives exactly the same class. -/
theorem admissible_iff_of_palette_agree {n : ℕ} {S T : Set ℕ}
    (h : ∀ d, d ≤ centralIndex n → (d ∈ S ↔ d ∈ T))
    {V : Type*} (A : Hyper n V) : Admissible S A ↔ Admissible T A := by
  constructor <;> intro hA f
  · exact (h _ (localIndex_le_central A f)).mp (hA f)
  · exact (h _ (localIndex_le_central A f)).mpr (hA f)

/-- A genuine strong amalgam on the standard carrier gives the original
finite-presentation SAP property after reindexing that carrier. -/
theorem local_hasStrongAmalgamation_of_strong_span {n : ℕ} (S : Set ℕ)
    (hspan : ∀ (a b c : ℕ)
      (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c))
      (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c),
      Preserves A B f → Preserves A C g → Admissible S B → Admissible S C →
      ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
        Admissible S D ∧ Preserves B D (FiniteStrongSpan.left f g) ∧
          Preserves C D (FiniteStrongSpan.right f g)) :
    HasStrongAmalgamation (localForbiddenFamily n S) := by
  classical
  intro a b c A B C _hA hB hC f g hf hg
  obtain ⟨D, hD, hi, hj⟩ := hspan a b c A B C f g hf hg
    ((omits_localForbiddenFamily_iff_admissible S B).mp hB)
    ((omits_localForbiddenFamily_iff_admissible S C).mp hC)
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let D' := D.pullback e.symm.toEmbedding
  let i := (FiniteStrongSpan.left f g).trans e.toEmbedding
  let j := (FiniteStrongSpan.right f g).trans e.toEmbedding
  refine ⟨Fintype.card (FiniteStrongSpan.Carrier f g), D', i, j,
    (omits_localForbiddenFamily_iff_admissible S D').mpr
      (admissible_pullback D e.symm.toEmbedding hD), ?_, ?_, ?_, ?_⟩
  · intro t
    have ht : (t.trans i).trans e.symm.toEmbedding =
        t.trans (FiniteStrongSpan.left f g) := by
      ext k
      simp [i]
    change D.orient ((t.trans i).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hi t
  · intro t
    have ht : (t.trans j).trans e.symm.toEmbedding =
        t.trans (FiniteStrongSpan.right f g) := by
      ext k
      simp [j]
    change D.orient ((t.trans j).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hj t
  · intro x
    exact congrArg e (FiniteStrongSpan.commutes f g x)
  · intro y z heq
    exact (FiniteStrongSpan.overlap f g y z).mp (e.injective heq)

/-- Forgetting the exact-overlap clause recovers ordinary AP of the same
admissible class. -/
theorem local_hasAP_of_hasStrongAmalgamation {n : ℕ} (S : Set ℕ)
    (h : HasStrongAmalgamation (localForbiddenFamily n S)) : HasAP n S := by
  intro a b c A B C hA hB hC f g hf hg
  obtain ⟨d, D, i, j, hD, hi, hj, hcomm, _hoverlap⟩ := h a b c A B C
    ((omits_localForbiddenFamily_iff_admissible S A).mpr hA)
    ((omits_localForbiddenFamily_iff_admissible S B).mpr hB)
    ((omits_localForbiddenFamily_iff_admissible S C).mpr hC) f g hf hg
  exact ⟨d, D, i, j, (omits_localForbiddenFamily_iff_admissible S D).mp hD,
    hi, hj, hcomm⟩

end Hypertournaments
