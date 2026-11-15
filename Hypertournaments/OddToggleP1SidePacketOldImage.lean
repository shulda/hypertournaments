import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1OmissionAllLinks

/-!
# Exact old-vertex content of a genuine p1 side packet

A side packet omitting old vertex v has all original old base vertices
except v and also the new last point. Erasing that last point
from the packet gives exactly the image of univ.erase v under the
canonical old-base inclusion.

This finite-set equality allows F₂ facet sums over the side
packet to be decomposed into one base sign and the complete
old-vertex link row, with no informal counting assumptions.
-/

namespace Hypertournaments

/-- After deleting the new endpoint from a side packet missing old v,
the remaining set is precisely all the other old base vertices. -/
theorem p1SidePacket_erase_last_eq_old_image
    (k : ℕ) (v : Fin (4*k+6)) :
    (p1SidePacketOmitOld k v).erase (Fin.last (4*k+6)) =
      ((Finset.univ : Finset (Fin (4*k+6))).erase v).image
        (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)) := by
  ext x
  rcases x.eq_castSucc_or_eq_last with ⟨t, rfl⟩ | rfl
  · have hnot :
        (t.castSucc : Fin (4*k+6+1)) ≠ Fin.last (4*k+6) :=
      Fin.castSucc_ne_last t
    constructor
    · intro hmem
      have htv : t ≠ v :=
        (p1SidePacketOmitOld_mem_old k v t).mp
          (Finset.mem_erase.mp hmem).2
      exact Finset.mem_image.mpr
        ⟨t, Finset.mem_erase.mpr ⟨htv, Finset.mem_univ _⟩, rfl⟩
    · intro hmem
      obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp hmem
      have he : u = t :=
        (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)).injective hut
      subst u
      have htv : t ≠ v := (Finset.mem_erase.mp hu).1
      exact Finset.mem_erase.mpr
        ⟨hnot, (p1SidePacketOmitOld_mem_old k v t).mpr htv⟩
  · have hnot := p1Last_not_mem_base_image k
        ((Finset.univ : Finset (Fin (4*k+6))).erase v)
    constructor
    · intro h
      exact False.elim ((Finset.mem_erase.mp h).1 rfl)
    · intro h
      exact False.elim (hnot h)

end Hypertournaments
