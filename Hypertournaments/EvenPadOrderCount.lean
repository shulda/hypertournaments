import Hypertournaments.EvenSuspensionSigns
import Hypertournaments.CanonicalPacket

/-!
# Identify padding vertices by their positions in the ordered sum

In the even-suspension convention all pad vertices precede all old
vertices. The abstract pad projection of any finite set therefore
agrees exactly with the filter by the numerical cutoff m. For an
injective tuple its cardinality is the number of tuple coordinates
below m. This prepares the h=2 and h=3 positional facet analysis.
-/

namespace Hypertournaments

/-- A high vertex is a pad precisely if its number is smaller than m. -/
theorem evenPadShift_mem_range_iff_lt
    (m k : ℕ) (v : Fin (m + k)) :
    v ∈ Set.range (evenPadShift m k) ↔ v.val < m := by
  constructor
  · rintro ⟨p, rfl⟩
    exact p.isLt
  · intro hv
    refine ⟨⟨v.val, hv⟩, ?_⟩
    apply Fin.ext
    rfl

/-- A high vertex comes from the old part iff its number is at least m. -/
theorem evenOldShift_mem_range_iff_ge
    (m k : ℕ) (v : Fin (m + k)) :
    v ∈ Set.range (evenOldShift m k) ↔ m ≤ v.val := by
  constructor
  · rintro ⟨u, rfl⟩
    change m ≤ m + u.val
    omega
  · intro hv
    refine ⟨⟨v.val - m, by
      have hlt := v.isLt
      omega⟩, ?_⟩
    apply Fin.ext
    change m + (v.val - m) = v.val
    omega

/-- The pad indices present in Q, transported back to high vertices,
are exactly the high vertices of Q below the pad cutoff. -/
theorem evenPadProjection_image_eq_filter
    (m k : ℕ) (Q : Finset (Fin (m + k))) :
    (evenPadProjection m k Q).image (evenPadShift m k) =
      Q.filter (fun v => v.val < m) := by
  classical
  ext v
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h
    subst v
    have hQ : evenPadShift m k p ∈ Q := by
      simpa [evenPadProjection] using hp
    exact Finset.mem_filter.mpr ⟨hQ, p.isLt⟩
  · intro h
    obtain ⟨hQ, hlt⟩ := Finset.mem_filter.mp h
    obtain ⟨p, hpv⟩ := (evenPadShift_mem_range_iff_lt m k v).2 hlt
    refine Finset.mem_image.mpr ⟨p, ?_, hpv⟩
    simp only [evenPadProjection, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpv]
    exact hQ

/-- The projection cardinality counts precisely the high vertices
of Q whose index is below m. -/
theorem evenPadProjection_card_eq_filter
    (m k : ℕ) (Q : Finset (Fin (m + k))) :
    (evenPadProjection m k Q).card =
      (Q.filter (fun v => v.val < m)).card := by
  have h := congrArg Finset.card (evenPadProjection_image_eq_filter m k Q)
  rw [Finset.card_image_of_injective _ (evenPadShift m k).injective] at h
  exact h

/-- For any injective tuple, the number of pads in its vertex set
equals the number of coordinates that lie below m. -/
theorem evenPadProjection_tupleVertices_card
    {r m k : ℕ} (f : Fin r ↪ Fin (m + k)) :
    (evenPadProjection m k (tupleVertices f)).card =
      (Finset.univ.filter (fun i : Fin r => (f i).val < m)).card := by
  classical
  rw [evenPadProjection_card_eq_filter]
  have heq :
      (tupleVertices f).filter (fun v => v.val < m) =
      (Finset.univ.filter (fun i : Fin r => (f i).val < m)).image f := by
    ext v
    simp only [tupleVertices, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hlt⟩
      refine ⟨i, ?_, hi⟩
      rw [hi]
      exact hlt
    · rintro ⟨i, hlt, hi⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [← hi]
      exact hlt
  rw [heq, Finset.card_image_of_injective _ f.injective]

end Hypertournaments
