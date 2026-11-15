import Hypertournaments.OddToggleP3QMinusOneOldSingletons
import Hypertournaments.OddToggleP3FreshOldMembership

/-!
# Genuine one-fresh q=m-1 packets have opposite-parity old singleton vertices

This is the exact bridge from the finite q=m-1 old-packet
block-label theorem to a genuine canonical increasing side packet:
* its fresh vertex is last;
* its first m+1 positions enumerate precisely the old vertices;
* every occupied old block transfers into that old subset;
* the two globally singleton block positions thus correspond to
  genuine old vertices of the side packet, with unchanged parity.

No actual Hyper age theorem is claimed here; the already certified
missing-singleton zero-facet theorem is the next interface.
-/

namespace Hypertournaments

/-- In a genuine one-fresh packet whose old vertices meet every
block except possibly one, there are two ACTUAL packet positions
x,y before the fresh vertex, of opposite parity, whose old
vertices are globally unique in their respective block labels.
The assumptions are stated in the packet's intrinsic old image,
not in a synthetic ordered word. -/
theorem p3CanonicalFresh_qMinusOne_singleton_positions
    (m t : ℕ) (hm : 6 ≤ m)
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hFresh : Fin.last (m*t) ∈ tupleVertices f.toEmbedding)
    (missing : Fin m)
    (hOthers : ∀ i : Fin m, i ≠ missing →
       ∃ v : Fin (m*t),
         v.castSucc ∈ tupleVertices f.toEmbedding ∧
         p3BlockNumber t v = i.val) :
    ∃ (x y : Fin (m+1)) (v w : Fin (m*t)),
      x.val%2=0 ∧ y.val%2=1 ∧
      v.castSucc = f x.castSucc ∧
      w.castSucc = f y.castSucc ∧
      (∀ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t z = p3BlockNumber t v → z=v) ∧
      (∀ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t z = p3BlockNumber t w → z=w) := by
  classical
  obtain ⟨U, hU, hEnum, hMem⟩ :=
    p3CanonicalFresh_old_enumeration_membership
      (m*t) (m+1) f hFresh
  have hOthersU : ∀ i : Fin m, i ≠ missing →
      0 < p3BlockOccupancy m t U i := by
    intro i hi
    obtain ⟨v, hv, hBlock⟩ := hOthers i hi
    have hvU : v ∈ U := (hMem v).mpr hv
    change 0 < (U.filter
      (fun z : Fin (m*t) => p3BlockNumber t z = i.val)).card
    apply Finset.card_pos.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvU, hBlock⟩⟩
  obtain ⟨x,y,hEven,hOdd,hSingleX,hSingleY⟩ :=
    p3Sorted_qMinusOne_oppositeParity_singletons
      m t hm U hU missing hOthersU
  let v : Fin (m*t) := U.orderEmbOfFin hU x
  let w : Fin (m*t) := U.orderEmbOfFin hU y
  have hV : v.castSucc = f x.castSucc := hEnum x
  have hW : w.castSucc = f y.castSucc := hEnum y
  have hSingletonX : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = p3BlockNumber t v → z=v := by
    intro z hz hBlock
    have hzU : z ∈ U := (hMem z).mpr hz
    have hzImage : z ∈ (Finset.univ : Finset (Fin (m+1))).image
          (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hzU
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hzImage
    have hSame :
        p3BlockNumber t (U.orderEmbOfFin hU q) =
          p3BlockNumber t (U.orderEmbOfFin hU x) := by
      rw [hq]
      exact hBlock
    have hqx : q = x := hSingleX q hSame
    calc
      z = U.orderEmbOfFin hU q := hq.symm
      _ = v := congrArg (U.orderEmbOfFin hU) hqx
  have hSingletonY : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = p3BlockNumber t w → z=w := by
    intro z hz hBlock
    have hzU : z ∈ U := (hMem z).mpr hz
    have hzImage : z ∈ (Finset.univ : Finset (Fin (m+1))).image
          (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hzU
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hzImage
    have hSame :
        p3BlockNumber t (U.orderEmbOfFin hU q) =
          p3BlockNumber t (U.orderEmbOfFin hU y) := by
      rw [hq]
      exact hBlock
    have hqy : q = y := hSingleY q hSame
    calc
      z = U.orderEmbOfFin hU q := hq.symm
      _ = w := congrArg (U.orderEmbOfFin hU) hqy
  exact ⟨x,y,v,w,hEven,hOdd,hV,hW,hSingletonX,hSingletonY⟩

end Hypertournaments
