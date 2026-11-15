import Mathlib.Tactic.Ext
import Hypertournaments.EvenTwoPadLocalIndexRecovery
import Hypertournaments.EvenSuspensionOrderedFacets

/-!
# Exact +1 type shift on prepared increasing two-pad packets

For any increasing old (n+1)-tuple and two increasing pads, its
actual high (n+3)-tuple is increasing. Deleting either of its two
pads leaves an all-positive one-pad facet, so both raw first facets
agree. The general intrinsic two-pad shift theorem then raises the
local type by one; the exact even-suspension source slice recovers
the original old local index.

This closes the algebraic shift for canonical increasing two-pad
packets. The separate representation theorem that every increasing
high packet with h=2 has this form remains open.
-/

namespace Hypertournaments

theorem Hyper.evenSuspension_localIndex_prepared_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (x y : Fin m) (hxy : x < y)
    (t : Fin (n + 1) ↪o Fin k) :
    localIndex (A.evenSuspension m k)
        (evenPaddedTuple m k x y hxy t.toEmbedding) =
      localIndex A t.toEmbedding + 1 := by
  let D : Hyper (n + 2) (Fin (m + k)) := A.evenSuspension m k
  let f : Fin (n + 3) ↪o Fin (m + k) :=
    OrderEmbedding.ofStrictMono
      (fun i : Fin (n + 3) =>
        evenPaddedTuple m k x y hxy t.toEmbedding i)
      (evenPaddedTuple_strictMono m k x y hxy t)
  have hf : f.toEmbedding = evenPaddedTuple m k x y hxy t.toEmbedding := by
    ext i
    rfl
  have htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2 := by
    rw [hf, evenPaddedTuple_vertices]
    exact evenPadProjection_paddedPacket_card m k x y _
      (ne_of_lt hxy)
  have hpx : x ∈ evenPadProjection m k (tupleVertices f.toEmbedding) := by
    rw [hf, evenPaddedTuple_vertices, evenPadProjection_paddedPacket]
    simp
  have hpy : y ∈ evenPadProjection m k (tupleVertices f.toEmbedding) := by
    rw [hf, evenPaddedTuple_vertices, evenPadProjection_paddedPacket]
    simp
  have hfx : f (0 : Fin (n + 3)) = evenPadShift m k x := by
    change evenPaddedTuple m k x y hxy t.toEmbedding 0 =
      evenPadShift m k x
    simp [evenPaddedTuple, twoPadSliceTuple]
  have hfy : f (1 : Fin (n + 3)) = evenPadShift m k y := by
    change evenPaddedTuple m k x y hxy t.toEmbedding 1 =
      evenPadShift m k y
    simp [evenPaddedTuple, twoPadSliceTuple]
  have h0 : D.orient (facet f.toEmbedding (0 : Fin (n + 3))) =
        true := by
    exact A.evenSuspension_orient_increasingFacet_pad_two
      f htwo x hpx 0 hfx
  have h1 : D.orient (facet f.toEmbedding (1 : Fin (n + 3))) =
        true := by
    exact A.evenSuspension_orient_increasingFacet_pad_two
      f htwo y hpy 1 hfy
  have hraw :
      D.orient
        (facet (evenPaddedTuple m k x y hxy t.toEmbedding) 0) =
      D.orient
        (facet (evenPaddedTuple m k x y hxy t.toEmbedding) 1) := by
    rw [← hf]
    exact h0.trans h1.symm
  have hshift :=
    localIndex_twoPadSlice_shift_of_raw_equal
      D (evenOldShift m k) (evenPadShift m k x) (evenPadShift m k y)
      (evenPadShift_not_mem_old m k x)
      (evenPadShift_not_mem_old m k y)
      (fun he => (ne_of_lt hxy) ((evenPadShift m k).injective he))
      t.toEmbedding hraw
  have hrecover :=
    Hyper.evenSuspension_twoPadSlice_localIndex
      m k A x y hxy t.toEmbedding
  exact hshift.trans (congrArg (fun d : ℕ => d + 1) hrecover)

end Hypertournaments
