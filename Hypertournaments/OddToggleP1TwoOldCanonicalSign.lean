import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1OmissionAllLinks
import Hypertournaments.OddToggleP1ActualRawCount
import Hypertournaments.CanonicalSignPresentation

/-!
# Genuine canonical n-facet orientations on p1 side packets omitting two old points

An actual side n-set contains its new endpoint and all but two
old vertices. Its true intrinsic canonical sign is exactly the
prescribed canonical link bit on that old pair. This fact holds
for either side in all exceptional arities n=4k+5, and is the
source-side input to the mixed-joint no-amalgamation obstruction.
-/

namespace Hypertournaments

/-- Deleting a second distinct old vertex from the full old-omission
side packet leaves exactly 4k+5 vertices, the side's n-ary arity. -/
theorem p1SideTwoOldPacket_card
    (k : ℕ) (v w : Fin (4*k+6)) (hvne : v ≠ w) :
    ((p1SidePacketOmitOld k v).erase w.castSucc).card = 4*k+5 := by
  have hmem : w.castSucc ∈ p1SidePacketOmitOld k v :=
    (p1SidePacketOmitOld_mem_old k v w).mpr hvne.symm
  have hcard := p1SidePacketOmitOld_card k v
  have he := Finset.card_erase_add_one hmem
  omega

/-- The canonical sign of the genuine intrinsic p1 side on
the n-set missing old v,w is literally the prescribed pair link. -/
theorem p1SideHyper_canonicalSignTable_two_old
    (k : ℕ) (left : Bool)
    (v w : Fin (4*k+6)) (hvne : v ≠ w) :
    (p1SideHyper k left).canonicalSignTable
      ((p1SidePacketOmitOld k v).erase w.castSucc) =
        p1CanonicalLink k left v w := by
  let S : Finset (Fin (4*k+6+1)) :=
    (p1SidePacketOmitOld k v).erase w.castSucc
  have hs : S.card = 4*k+5 := p1SideTwoOldPacket_card k v w hvne
  let g : Fin (4*k+5) ↪o Fin (4*k+6+1) := S.orderEmbOfFin hs
  have hverts : tupleVertices g.toEmbedding = S := by
    simpa [tupleVertices, g] using
      (Finset.image_orderEmbOfFin_univ S hs)
  calc
    (p1SideHyper k left).canonicalSignTable S =
        (p1SideHyper k left).orient g.toEmbedding :=
      (p1SideHyper k left).canonicalSignTable_at S hs
    _ = p1SideSignTable k left S := by
      change (Hyper.fromOrderedSigns
        (p1SideSignTable k left)).orient g.toEmbedding =
          p1SideSignTable k left S
      rw [fromOrderedSigns_orient_strictMono
        (p1SideSignTable k left) g.toEmbedding g.strictMono, hverts]
    _ = p1CanonicalLink k left v w :=
      p1SidePacket_sign_erase_old_ne k left v w hvne

end Hypertournaments
