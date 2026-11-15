import Hypertournaments.FiveConstrained.Normalization
import Hypertournaments.FiveConstrained.ClassRecognition
import Hypertournaments.FiveConstrained.P9Consequences
import Hypertournaments.SmallArityClassification
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Positive cases of the five-constrained classification

The four previously formalized local classes and the concrete `P9` omission
class are identified with the actual normalized four/five predicates.
-/

namespace Hypertournaments.FiveConstrained

/-- A four-condition implies the five-condition when every compatible named
packet is prescribed. The finite instances below discharge this premise. -/
theorem fiveAllowed_of_admissible (four five : ℕ)
    (hcover : ∀ t : Fin 12,
      (∀ d : Fin 3, (support4 t).testBit d.val = true →
        four.testBit d.val = true) → five.testBit t.val = true)
    {V : Type*} (A : Hyper 3 V) (hA : Admissible (fourPalette four) A) :
    FiveAllowed five A := by
  intro e
  let F := A.pullback e
  let t := type5 (encode5 F)
  obtain ⟨σ, hσ⟩ := exists_representative F
  have hF : Admissible (fourPalette four) F :=
    admissible_of_preserves (fun _ => rfl) hA
  have hrep : Admissible (fourPalette four) (maskHyper 5 (representative t)) :=
    admissible_of_preserves hσ hF
  refine ⟨t, hcover t ?_, σ, hσ⟩
  intro d hd
  obtain ⟨f, hf⟩ := (support4_correct t (by omega : d.val ≤ 2)).mp hd
  simpa [fourPalette, hf] using hrep f

private theorem familiar_cover :
    ∀ p : Fin 4, ∀ t : Fin 12,
      (∀ d : Fin 3, (support4 t).testBit d.val = true →
        (#[4, 6, 5, 7][p.val]!).testBit d.val = true) →
      (#[1, 119, 257, 4095][p.val]!).testBit t.val = true := by decide

private theorem familiar_supports :
    ∀ p : Fin 4,
      certificateSupport4 (#[1, 119, 257, 4095][p.val]!) =
        #[4, 6, 5, 7][p.val]! := by decide

theorem normalized_familiar_iff {V : Type*} (p : Fin 4)
    (A : Hyper 3 V) :
    Constrained (certificateSupport4 (#[1, 119, 257, 4095][p.val]!))
      (#[1, 119, 257, 4095][p.val]!) A ↔
        Admissible (fourPalette (#[4, 6, 5, 7][p.val]!)) A := by
  rw [familiar_supports p]
  exact ⟨fun h => h.1, fun h =>
    ⟨h, fiveAllowed_of_admissible _ _ (familiar_cover p) A h⟩⟩

theorem normalized_cyclic_iff {V : Type*} (A : Hyper 3 V) :
    Constrained (certificateSupport4 1) 1 A ↔ Admissible {2} A := by
  have h := normalized_familiar_iff 0 A
  change Constrained (certificateSupport4 1) 1 A ↔ Admissible (fourPalette 4) A at h
  refine h.trans (admissible_iff_of_palette_agree ?_ A)
  intro d hd
  have hc : d = 0 ∨ d = 1 ∨ d = 2 := by
    change d ≤ 2 at hd
    omega
  rcases hc with rfl | rfl | rfl <;> simp [fourPalette] <;> decide

theorem normalized_h4free_iff {V : Type*} (A : Hyper 3 V) :
    Constrained (certificateSupport4 119) 119 A ↔ Admissible {1, 2} A := by
  have h := normalized_familiar_iff 1 A
  change Constrained (certificateSupport4 119) 119 A ↔ Admissible (fourPalette 6) A at h
  refine h.trans (admissible_iff_of_palette_agree ?_ A)
  intro d hd
  have hc : d = 0 ∨ d = 1 ∨ d = 2 := by
    change d ≤ 2 at hd
    omega
  rcases hc with rfl | rfl | rfl <;> simp [fourPalette] <;> decide

theorem normalized_even_iff {V : Type*} (A : Hyper 3 V) :
    Constrained (certificateSupport4 257) 257 A ↔ Admissible {0, 2} A := by
  have h := normalized_familiar_iff 2 A
  change Constrained (certificateSupport4 257) 257 A ↔ Admissible (fourPalette 5) A at h
  refine h.trans (admissible_iff_of_palette_agree ?_ A)
  intro d hd
  have hc : d = 0 ∨ d = 1 ∨ d = 2 := by
    change d ≤ 2 at hd
    omega
  rcases hc with rfl | rfl | rfl <;> simp [fourPalette] <;> decide

theorem packetAllowed_p9_iff (A : Hyper 3 (Fin 5)) :
    PacketAllowed 3583 A ↔
      ¬ ∃ σ : Equiv.Perm (Fin 5), Preserves p9 A σ.toEmbedding := by
  rw [packetAllowed_iff_type5]
  have hbit : ∀ t : Fin 12, (3583 : ℕ).testBit t.val = true ↔ t ≠ 9 := by decide
  rw [hbit]
  have hiso := representative_iso_iff_type5 A 9
  change (∃ σ : Equiv.Perm (Fin 5), Preserves p9 A σ.toEmbedding) ↔
      type5 (encode5 A) = 9 at hiso
  exact not_congr hiso.symm

theorem fiveAllowed_p9_iff {V : Type*} (A : Hyper 3 V) :
    FiveAllowed 3583 A ↔ Omits p9Family A := by
  rw [omits_p9Family_iff]
  constructor
  · intro h e he
    apply (packetAllowed_p9_iff (A.pullback e)).mp (h e)
    exact ⟨1, he⟩
  · intro h e
    apply (packetAllowed_p9_iff (A.pullback e)).mpr
    rintro ⟨σ, hσ⟩
    exact h (σ.toEmbedding.trans e) hσ

private theorem admissible_seven {V : Type*} (A : Hyper 3 V) :
    Admissible (fourPalette 7) A := by
  intro e
  have hle : localIndex A e ≤ 2 := localIndex_le_central A e
  have h : localIndex A e = 0 ∨ localIndex A e = 1 ∨ localIndex A e = 2 := by omega
  rcases h with h | h | h <;> simp [fourPalette, h] <;> decide

theorem normalized_p9_iff {V : Type*} (A : Hyper 3 V) :
    Constrained (certificateSupport4 3583) 3583 A ↔ Omits p9Family A := by
  have hs : certificateSupport4 3583 = 7 := by decide
  rw [hs]
  exact ⟨fun h => (fiveAllowed_p9_iff A).mp h.2,
    fun h => ⟨admissible_seven A, (fiveAllowed_p9_iff A).mpr h⟩⟩

theorem normalized_p9_hasSAP : (normalizedClass 3583).HasSAP := by
  apply (FiniteClass.hasSAP_congr (fun _ A => normalized_p9_iff A)).mpr
  exact (FiniteClass.hasSAP_omits_iff p9Family).mpr p9_hasStrongAmalgamation

theorem normalized_familiar_hasSAP (p : Fin 4) :
    (normalizedClass (#[1, 119, 257, 4095][p.val]!)).HasSAP := by
  apply (FiniteClass.hasSAP_congr (fun _ A => normalized_familiar_iff p A)).mpr
  let S := fourPalette (#[4, 6, 5, 7][p.val]!)
  have hcentral : centralIndex 3 ∈ S := by
    change (#[4, 6, 5, 7][p.val]!).testBit 2 = true
    have h : ∀ p : Fin 4, (#[4, 6, 5, 7][p.val]!).testBit 2 = true := by decide
    exact h p
  have hSAP := small_arity_unbounded_hasStrongAmalgamation
    (n := 3) (by decide) (by decide) S
    ((unboundedAdmissible_iff_central 3 S).mpr hcentral)
  apply (FiniteClass.hasSAP_congr
    (fun _ A => omits_localForbiddenFamily_iff_admissible S A)).mp
  exact (FiniteClass.hasSAP_omits_iff (localForbiddenFamily 3 S)).mpr hSAP

/-- Every surviving finite palette has an actual strong amalgamation proof. -/
theorem normalized_positive_hasSAP {palette : ℕ}
    (h : certificatePositive palette = true) : (normalizedClass palette).HasSAP := by
  have hp : palette = 1 ∨ palette = 119 ∨ palette = 257 ∨
      palette = 3583 ∨ palette = 4095 := by
    simpa [certificatePositive, Bool.or_eq_true, or_assoc] using h
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact normalized_familiar_hasSAP 0
  · exact normalized_familiar_hasSAP 1
  · exact normalized_familiar_hasSAP 2
  · exact normalized_p9_hasSAP
  · exact normalized_familiar_hasSAP 3

end Hypertournaments.FiveConstrained
