import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.EvenPadOrderCount

/-!
# Canonical projections of the old coordinates in a padded tuple

The old vertex projection is exactly the complementary numerical
cutoff to the padding vertex projection. Its cardinality equals the
number of old-coordinate positions in any injective ambient tuple.
These lemmas are uniform in arity and independent of orientation.

They are needed for the three-pad root-absent packet: to identify
the old n-set of an (n+3)-tuple, and to append the distinguished root
before its increasing enumeration.
-/

namespace Hypertournaments

/-- Transporting the old projection to ambient vertices picks out
precisely those ambient vertices at or beyond the padding cutoff. -/
theorem evenOldProjection_image_eq_filter (m k : ℕ)
    (Q : Finset (Fin (m + k))) :
    (evenOldProjection m k Q).image (evenOldShift m k) =
      Q.filter (fun v => m ≤ v.val) := by
  classical
  ext v
  constructor
  · intro h
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp h
    subst v
    have hQ : evenOldShift m k u ∈ Q := by
      simpa [evenOldProjection] using hu
    exact Finset.mem_filter.mpr ⟨hQ, by
      change m ≤ m + u.val
      omega⟩
  · intro h
    obtain ⟨hQ, hge⟩ := Finset.mem_filter.mp h
    obtain ⟨u, huv⟩ :=
      (evenOldShift_mem_range_iff_ge m k v).2 hge
    refine Finset.mem_image.mpr ⟨u, ?_, huv⟩
    simp only [evenOldProjection, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [huv]
    exact hQ

/-- The actual old vertex projection has the same size as the
ambient subset restricted to vertices at or beyond m. -/
theorem evenOldProjection_card_eq_filter (m k : ℕ)
    (Q : Finset (Fin (m + k))) :
    (evenOldProjection m k Q).card =
      (Q.filter (fun v => m ≤ v.val)).card := by
  have h := congrArg Finset.card (evenOldProjection_image_eq_filter m k Q)
  rw [Finset.card_image_of_injective _ (evenOldShift m k).injective] at h
  exact h

/-- The number of old vertices of an arbitrary injective ambient
tuple is precisely the number of its coordinates at or beyond m. -/
theorem evenOldProjection_tupleVertices_card
    {r m k : ℕ} (f : Fin r ↪ Fin (m + k)) :
    (evenOldProjection m k (tupleVertices f)).card =
      (Finset.univ.filter (fun i : Fin r => m ≤ (f i).val)).card := by
  classical
  rw [evenOldProjection_card_eq_filter]
  have heq :
      (tupleVertices f).filter (fun v => m ≤ v.val) =
      (Finset.univ.filter (fun i : Fin r => m ≤ (f i).val)).image f := by
    ext v
    simp only [tupleVertices, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hge⟩
      refine ⟨i, ?_, hi⟩
      rw [hi]
      exact hge
    · rintro ⟨i, hge, hi⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [← hi]
      exact hge
  rw [heq, Finset.card_image_of_injective _ f.injective]

end Hypertournaments
