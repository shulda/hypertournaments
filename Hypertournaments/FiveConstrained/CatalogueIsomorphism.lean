import Hypertournaments.FiveConstrained.CatalogueInvariant
import Hypertournaments.FiveConstrained.CatalogueRecognition

namespace Hypertournaments.FiveConstrained

theorem representative_lt (t : Fin 12) : representative t < 1024 := by
  have h : ∀ t : Fin 12, representative t < 1024 := by decide
  exact h t

/-- Completeness of the catalogue on actual intrinsic five-vertex structures. -/
theorem exists_representative (A : Hyper 3 (Fin 5)) :
    ∃ σ : Equiv.Perm (Fin 5),
      Preserves (maskHyper 5 (representative (type5 (encode5 A)))) A σ.toEmbedding := by
  let m : Fin 1024 := ⟨encode5 A, encode5_lt A⟩
  refine ⟨orbitWitnessPerm m, ?_⟩
  intro t
  rw [← maskHyper_encode5 A (t.trans (orbitWitnessPerm m).toEmbedding)]
  exact orbitWitness_preserves m t

/-- Catalogue recognition is exactly actual orientation-preserving isomorphism. -/
theorem representative_iso_iff_type5 (A : Hyper 3 (Fin 5)) (t : Fin 12) :
    (∃ σ : Equiv.Perm (Fin 5),
      Preserves (maskHyper 5 (representative t)) A σ.toEmbedding) ↔
        type5 (encode5 A) = t := by
  constructor
  · rintro ⟨σ, hp⟩
    have h := type5_encode5_preserves (maskHyper 5 (representative t)) A σ hp
    rw [encode5_maskHyper ⟨representative t, representative_lt t⟩,
      type5_representative] at h
    exact h.symm
  · intro h
    obtain ⟨σ, hp⟩ := exists_representative A
    exact ⟨σ, by simpa only [h] using hp⟩

/-- Named representatives are isomorphic exactly when their indices agree. -/
theorem representative_iso_iff (s t : Fin 12) :
    (∃ σ : Equiv.Perm (Fin 5),
      Preserves (maskHyper 5 (representative s))
        (maskHyper 5 (representative t)) σ.toEmbedding) ↔ s = t := by
  rw [representative_iso_iff_type5,
    encode5_maskHyper ⟨representative t, representative_lt t⟩, type5_representative]
  exact eq_comm

end Hypertournaments.FiveConstrained
