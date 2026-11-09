import Hypertournaments.EvenSuspensionSigns
import Hypertournaments.Obstruction

/-!
# Suspension projections commute with the canonical common-base embedding

Adding a new last old vertex to a finite source changes neither the
locations of the original pads nor the old vertices. We verify that
both pad and old projections of arbitrary padded finite subsets
commute exactly with the canonical one-point base inclusion.

These geometric equalities are the first step toward proving that
even suspension respects a genuine ordinary one-point AP diagram.
They are independent of the old orientation and its admissibility.
-/

namespace Hypertournaments

/-- The pad injections commute with adjoining a last old vertex. -/
theorem evenPadShift_base_compat (m k : ℕ) (p : Fin m) :
    evenPadShift m (k + 1) p =
      onePointBaseEmbedding (m + k) (evenPadShift m k p) := by
  apply Fin.ext
  rfl

/-- The old injections commute with adjoining a last old vertex. -/
theorem evenOldShift_base_compat (m k : ℕ) (u : Fin k) :
    evenOldShift m (k + 1) (onePointBaseEmbedding k u) =
      onePointBaseEmbedding (m + k) (evenOldShift m k u) := by
  apply Fin.ext
  rfl

/-- Padding-vertex projection is literally invariant under inclusion
of a finite padded source into its one-point extension. -/
theorem evenPadProjection_image_base (m k : ℕ)
    (Q : Finset (Fin (m + k))) :
    evenPadProjection m (k + 1)
      (Q.image (onePointBaseEmbedding (m + k))) =
    evenPadProjection m k Q := by
  classical
  ext p
  simp only [evenPadProjection, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [evenPadShift_base_compat]
  constructor
  · intro hx
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
    have he : u = evenPadShift m k p :=
      (onePointBaseEmbedding (m + k)).injective heq
    simpa [he] using hu
  · intro hp
    exact Finset.mem_image.mpr ⟨evenPadShift m k p, hp, rfl⟩

/-- The old-vertex projection commutes with the final-vertex inclusion,
and cannot accidentally acquire the new last old vertex. -/
theorem evenOldProjection_image_base (m k : ℕ)
    (Q : Finset (Fin (m + k))) :
    evenOldProjection m (k + 1)
      (Q.image (onePointBaseEmbedding (m + k))) =
    (evenOldProjection m k Q).image (onePointBaseEmbedding k) := by
  classical
  ext u
  simp only [evenOldProjection, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases u.eq_castSucc_or_eq_last with ⟨v, rfl⟩ | rfl
  · have hshift := evenOldShift_base_compat m k v
    change
      evenOldShift m (k + 1) (onePointBaseEmbedding k v) ∈
        Q.image (onePointBaseEmbedding (m + k)) ↔
      onePointBaseEmbedding k v ∈
        (evenOldProjection m k Q).image (onePointBaseEmbedding k)
    rw [hshift]
    constructor
    · intro h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      have he : w = evenOldShift m k v :=
        (onePointBaseEmbedding (m + k)).injective heq
      have hmem : v ∈ evenOldProjection m k Q := by
        change evenOldShift m k v ∈ Q
        simpa [he] using hw
      exact Finset.mem_image.mpr ⟨v, hmem, rfl⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      have he : w = v := (onePointBaseEmbedding k).injective heq
      have hmem : evenOldShift m k v ∈ Q := by
        have hv : v ∈ evenOldProjection m k Q := by
          simpa [he] using hw
        exact hv
      exact Finset.mem_image.mpr ⟨evenOldShift m k v, hmem, rfl⟩
  · have hL :
        evenOldShift m (k + 1) (Fin.last k) ∉
          Q.image (onePointBaseEmbedding (m + k)) := by
      intro hx
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hx
      have hv := congrArg Fin.val heq
      have hbound := w.isLt
      change w.val = m + k at hv
      omega
    have hR :
        Fin.last k ∉
          (evenOldProjection m k Q).image (onePointBaseEmbedding k) := by
      intro hx
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hx
      have hv := congrArg Fin.val heq
      have hbound := w.isLt
      change w.val = k at hv
      omega
    change
      evenOldShift m (k + 1) (Fin.last k) ∈
        Q.image (onePointBaseEmbedding (m + k)) ↔
      Fin.last k ∈
        (evenOldProjection m k Q).image (onePointBaseEmbedding k)
    exact iff_false_intro hL hR

end Hypertournaments
