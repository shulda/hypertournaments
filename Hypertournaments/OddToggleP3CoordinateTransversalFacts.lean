import Hypertournaments.OddToggleP3CoordinateTransversals

/-!
# Coordinate tuples are genuine full old-block transversals

The zero-sum code has previously been formalized abstractly over
an additive group G. For G = ZMod t, the actual old vertex map
i ↦ i*t + val(q i) has now been constructed and shown injective
across different block labels.

Here we establish that each selected actual finite old subset
is exactly a p3IsBlockTransversal, with one old vertex in EVERY
consecutive block, and that the entire coordinate tuple can be
recovered from its old vertex set. Consequently any subset of
the zero-sum code yields different real p3 full transversals.

This is a substantive correspondence between abstract independent
source indices and actual old subsets of p3CanonicalSide.
The punctured-coordinate source-identity is the next obligation.
-/

namespace Hypertournaments

/-- In the selected actual old transversal, the complete
fiber of old block i is exactly the singleton consisting
of the vertex encoded by coordinate q(i). -/
theorem p3CoordinateTransversal_block_fiber
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) (i : Fin m) :
    (p3CoordinateTransversal m t ht q).filter
      (fun v => p3BlockNumber t v = i.val) =
    {p3BlockCoordinateVertex m t ht i (q i)} := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨j, _, hj⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).1
    have hlabel := (Finset.mem_filter.mp hv).2
    have hjblock :
        j.val = i.val := by
      have heq : p3BlockNumber t
          (p3BlockCoordinateVertex m t ht j (q j)) =
          i.val := by
        rw [hj]
        exact hlabel
      simpa only [p3BlockCoordinateVertex_blockNumber] using heq
    have hji : j = i := Fin.ext hjblock
    subst j
    exact Finset.mem_singleton.mpr hj
  · intro hv
    have hvEq : v = p3BlockCoordinateVertex m t ht i (q i) :=
      Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        p3BlockCoordinateVertex_blockNumber m t ht i (q i)⟩

/-- The actual selected old subset satisfies exactly the
same p3 full-block-transversal predicate used by the genuine
canonical side W-potential, not merely a numerical count. -/
theorem p3CoordinateTransversal_isBlockTransversal
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) :
    p3IsBlockTransversal m t
      (p3CoordinateTransversal m t ht q) := by
  constructor
  · exact p3CoordinateTransversal_card m t ht q
  · intro i
    change ((p3CoordinateTransversal m t ht q).filter
      (fun v => p3BlockNumber t v = i.val)).card = 1
    rw [p3CoordinateTransversal_block_fiber]
    simp

/-- The actual finite old set uniquely determines its FULL
block-coordinate word. Different zero-sum tuples therefore
choose genuinely different old m-element transversal sets. -/
theorem p3CoordinateTransversal_injective
    (m t : ℕ) (ht : 0 < t) :
    Function.Injective (p3CoordinateTransversal m t ht) := by
  intro q r hU
  funext i
  let v : Fin (m*t) := p3BlockCoordinateVertex m t ht i (q i)
  have hvR : v ∈ p3CoordinateTransversal m t ht r := by
    rw [← hU]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvR
  have hlabel := congrArg (p3BlockNumber t) hj
  have hji : j = i := by
    apply Fin.ext
    simpa only [p3BlockCoordinateVertex_blockNumber] using hlabel
  subst j
  have heq :
      p3BlockCoordinateVertex m t ht i (r i) =
      p3BlockCoordinateVertex m t ht i (q i) := hj
  exact (p3BlockCoordinateVertex_injective_coordinate
    m t ht i) heq.symm

end Hypertournaments
