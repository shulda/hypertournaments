import Hypertournaments.OddToggleP1Homogeneous
import Hypertournaments.CanonicalPacket

/-!
# Alternating raw orientations of genuine homogeneous packets

The homogeneous local type is localIndex = 0. By the kernel-checked
Boolean minority statistic, all normalized facets then share one
Boolean phase b. Undoing the normalization shows that the intrinsic
orientations along the increasing tuple's facets alternate with the
deletion index parity. This is the geometric input to the abstract
no-three-homogeneous-facets phase argument.
-/

namespace Hypertournaments

/-- Every actual homogeneous (n+1)-packet has alternating raw
orientations on its increasing facet indices, with some phase b. -/
theorem Hyper.localIndex_zero_raw_alternating
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (hzero : localIndex A f.toEmbedding = 0) :
    ∃ b : Bool, ∀ i : Fin (n+1),
      A.orient (facet f.toEmbedding i) =
        b ^^ decide (i.val%2=1) := by
  obtain ⟨b, hb⟩ :=
    (localIndex_zero_iff_normalized_constant A f.toEmbedding).mp hzero
  refine ⟨b, ?_⟩
  intro i
  have hn : A.orient (facet f.toEmbedding i) ^^
      decide (i.val%2=1) = b := hb i
  cases hraw : A.orient (facet f.toEmbedding i) <;>
    cases hpar : decide (i.val%2=1) <;>
    cases b <;> simp_all [normalizedFacet]

/-- For an increasing actual homogeneous packet, the canonical
unordered sign table on its facets has exactly the same alternating
raw phase. -/
theorem Hyper.localIndex_zero_canonical_sign_alternating
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (hzero : localIndex A f.toEmbedding = 0) :
    ∃ b : Bool, ∀ i : Fin (n+1),
      A.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) =
        b ^^ decide (i.val%2=1) := by
  obtain ⟨b, hb⟩ := A.localIndex_zero_raw_alternating f hzero
  refine ⟨b, ?_⟩
  intro i
  calc
    A.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) =
        (Hyper.fromOrderedSigns A.canonicalSignTable).orient
          (facet f.toEmbedding i) :=
      (fromOrderedSigns_facet_increasing A.canonicalSignTable f i).symm
    _ = A.orient (facet f.toEmbedding i) :=
      A.from_canonicalSignTable_orient (facet f.toEmbedding i)
    _ = b ^^ decide (i.val%2=1) := hb i

end Hypertournaments
