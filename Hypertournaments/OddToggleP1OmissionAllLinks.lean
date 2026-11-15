import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Tauto
import Hypertournaments.OddToggleP1OmissionFacets
import Hypertournaments.OddToggleP1CanonicalLinkSymmetry

/-!
# Side facet link signs for old omissions in both orders

The link sign on a genuine side packet omitting old base vertex v,
after deleting any other old base vertex w, is precisely the
canonical unordered pair link(v,w). The original exact facet
lemma treats v < w; here we use the certified symmetric link
table and the symmetry of a two-element Finset to cover w < v.

This supplies the all-old-vertex raw facet word needed for actual
side admissibility and mixed amalgamation constraints.
-/

namespace Hypertournaments

theorem p1SidePacket_sign_erase_old_ne (k : ℕ)
    (left : Bool) (v w : Fin (4*k+6)) (hne : v ≠ w) :
    p1SideSignTable k left
      ((p1SidePacketOmitOld k v).erase w.castSucc) =
      p1CanonicalLink k left v w := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact p1SidePacket_sign_erase_old k left v w hlt
  · have hend :
        Fin.last (4*k+6) ∈
          (p1SidePacketOmitOld k v).erase w.castSucc := by
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        have hv := congrArg Fin.val he
        have hw := w.isLt
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      · exact p1SidePacketOmitOld_last k v
    have hmissing := p1SidePacket_missing_two_old k v w
    have hpair : ({v,w} : Finset (Fin (4*k+6))) = {w,v} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    unfold p1SideSignTable
    rw [if_pos hend, hmissing, hpair,
      p1PairMissingBit_pair k left w v hgt,
      p1CanonicalLink_symmetric k left w v]

end Hypertournaments
