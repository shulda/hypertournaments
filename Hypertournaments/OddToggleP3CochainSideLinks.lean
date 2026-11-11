import Hypertournaments.Cochain

/-!
# Exact parity identity for the left and right potential links

In the n congruent to 3 modulo 4 exceptional construction, a
common base potential z_B extends to potential z_L after adding
the left new vertex l and to z_R after adding the right new
vertex r. Their one-point link orientations are the respective
coboundaries on insert l Q and insert r Q.

If the two potential tables agree on a base set Q, then the
sum of these two links is the coboundary of their combined
contracted cochain. This is the exact identity alpha+beta=delta h
used to gauge all parity-respecting mixed completions.

There are no random choices or AP conclusions in this lemma.
-/

namespace Hypertournaments

/-- The sum of two ZMod 2-valued finite-set cochain coboundaries
is the coboundary of their pointwise sum. -/
theorem p3Coboundary_add {V : Type*} [DecidableEq V]
    (g h : Finset V → ZMod 2) (Q : Finset V) :
    coboundary (fun U => g U + h U) Q =
      coboundary g Q + coboundary h Q := by
  simp only [coboundary, Finset.sum_add_distrib]

/-- When left and right potential tables agree on a base m-set Q,
their one-point link bits sum to the boundary of the combined
cone contractions. All facets and potential values are genuine
finite-set expressions. -/
theorem p3SideLink_sum_eq_coboundary
    {V : Type*} [DecidableEq V]
    (l r : V) (zL zR : Finset V → ZMod 2)
    (Q : Finset V) (hl : l ∉ Q) (hr : r ∉ Q)
    (hbase : zL Q = zR Q) :
    coboundary zL (insert l Q) +
        coboundary zR (insert r Q) =
      coboundary
        (fun U => contractAt l zL U + contractAt r zR U) Q := by
  have hleft := coboundary_insert_eq_add_contractAt l zL Q hl
  have hright := coboundary_insert_eq_add_contractAt r zR Q hr
  have hzero : zL Q + zR Q = 0 := by
    rw [← hbase]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      zL Q + zL Q = (2 : ZMod 2) * zL Q := by ring
      _ = 0 := by rw [h2]; simp
  calc
    coboundary zL (insert l Q) + coboundary zR (insert r Q) =
        (zL Q + coboundary (contractAt l zL) Q) +
        (zR Q + coboundary (contractAt r zR) Q) := by
          rw [hleft, hright]
    _ = (zL Q + zR Q) +
        (coboundary (contractAt l zL) Q +
         coboundary (contractAt r zR) Q) := by abel
    _ = coboundary (contractAt l zL) Q +
        coboundary (contractAt r zR) Q := by rw [hzero]; simp
    _ = coboundary
        (fun U => contractAt l zL U + contractAt r zR U) Q :=
          (p3Coboundary_add _ _ Q).symm

end Hypertournaments
