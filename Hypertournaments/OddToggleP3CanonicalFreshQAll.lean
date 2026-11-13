import Hypertournaments.OddToggleP3ActualFullBlockTriple
import Hypertournaments.OddToggleP3FreshOldMembership

/-!
# Every genuine q=m fresh packet has protected singleton old vertices of opposite parity

The preceding full-block old-subset theorem produces two opposite-
parity globally singleton vertices among any chosen three consecutive
old block labels. Here we transfer that result through the exact old
prefix enumeration of a genuine canonical increasing packet containing
the fresh point. No vertices are added or lost; their block numbers,
singleton uniqueness, and deletion-position parities are preserved.

The resulting statement uses actual packet vertex membership and
actual old-vertex identities. Turning these protected singleton
positions into raw-zero Hyper facets and exceptional age membership
is the next lemma.
-/

namespace Hypertournaments

/-- Actual canonical one-fresh packets with ALL old blocks occupied
have globally singleton old vertices at opposite deletion parities
inside any selected consecutive triple of block labels. -/
theorem p3CanonicalFresh_qAll_protected_singleton_positions
    (m t : ℕ) (ht : 0 < t)
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hFresh : Fin.last (m*t) ∈ tupleVertices f.toEmbedding)
    (hAll : ∀ i : Fin m,
      ∃ v : Fin (m*t),
        v.castSucc ∈ tupleVertices f.toEmbedding ∧
        p3BlockNumber t v = i.val)
    (start : ℕ) (hstart : start+2 < m) :
    ∃ (x y : Fin (m+1)) (v w : Fin (m*t)),
      x.val%2 ≠ y.val%2 ∧
      (start ≤ p3BlockNumber t v ∧
        p3BlockNumber t v ≤ start+2) ∧
      (start ≤ p3BlockNumber t w ∧
        p3BlockNumber t w ≤ start+2) ∧
      v.castSucc = f x.castSucc ∧
      w.castSucc = f y.castSucc ∧
      (∀ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t z = p3BlockNumber t v → z=v) ∧
      (∀ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t z = p3BlockNumber t w → z=w) := by
  classical
  obtain ⟨U,hU,hEnum,hMem⟩ :=
    p3CanonicalFresh_old_enumeration_membership
      (m*t) (m+1) f hFresh
  have hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i := by
    intro i
    obtain ⟨z,hz,hBlock⟩ := hAll i
    have hzU : z ∈ U := (hMem z).mpr hz
    change 0 < (U.filter
      (fun w : Fin (m*t) => p3BlockNumber t w = i.val)).card
    exact Finset.card_pos.mpr
      ⟨z,Finset.mem_filter.mpr ⟨hzU,hBlock⟩⟩
  obtain ⟨x,y,hParity,hRangeX,hRangeY,hSingleX,hSingleY⟩ :=
    p3ActualOneFresh_sorted_protectedTriple_singletons
      m t ht U hU hall start hstart
  let v : Fin (m*t) := U.orderEmbOfFin hU x
  let w : Fin (m*t) := U.orderEmbOfFin hU y
  have hV : v.castSucc = f x.castSucc := hEnum x
  have hW : w.castSucc = f y.castSucc := hEnum y
  have hSingletonV : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = p3BlockNumber t v → z=v := by
    intro z hz hBlock
    have hzU : z ∈ U := (hMem z).mpr hz
    have hzImage : z ∈ (Finset.univ : Finset (Fin (m+1))).image
        (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hzU
    obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hzImage
    have hSame :
        p3BlockNumber t (U.orderEmbOfFin hU q) =
          p3BlockNumber t (U.orderEmbOfFin hU x) := by
      rw [hq]
      exact hBlock
    have hEq : q = x := hSingleX q hSame
    calc
      z = U.orderEmbOfFin hU q := hq.symm
      _ = v := congrArg (U.orderEmbOfFin hU) hEq
  have hSingletonW : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = p3BlockNumber t w → z=w := by
    intro z hz hBlock
    have hzU : z ∈ U := (hMem z).mpr hz
    have hzImage : z ∈ (Finset.univ : Finset (Fin (m+1))).image
        (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hzU
    obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hzImage
    have hSame :
        p3BlockNumber t (U.orderEmbOfFin hU q) =
          p3BlockNumber t (U.orderEmbOfFin hU y) := by
      rw [hq]
      exact hBlock
    have hEq : q = y := hSingleY q hSame
    calc
      z = U.orderEmbOfFin hU q := hq.symm
      _ = w := congrArg (U.orderEmbOfFin hU) hEq
  exact ⟨x,y,v,w,hParity,hRangeX,hRangeY,hV,hW,
    hSingletonV,hSingletonW⟩

end Hypertournaments
