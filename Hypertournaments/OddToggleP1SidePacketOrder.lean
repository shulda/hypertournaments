import Hypertournaments.OddToggleP1OmissionFacets
import Hypertournaments.CanonicalPacket

/-!
# Exact increasing enumeration of an old-omission p1 side packet

The side vertex set is Fin(a+1), and the side packet missing the
old vertex v is univ.erase(v.castSucc), of size a. Its increasing
enumeration is therefore precisely the canonical order embedding
Fin.succAboveEmb(v.castSucc) : Fin a ↪o Fin(a+1).

This is an exact ordered-coordinate bridge, useful for translating
the protected a0/a4 homogeneous rows from raw pair-link signs to
actual normalized packet facets, with no hidden order convention.
-/

namespace Hypertournaments

theorem p1SidePacket_orderEmb_eq_succAbove
    (k : ℕ) (v : Fin (4*k+6))
    (hQ : (p1SidePacketOmitOld k v).card = 4*k+6) :
    (p1SidePacketOmitOld k v).orderEmbOfFin hQ =
      Fin.succAboveEmb (v.castSucc : Fin (4*k+6+1)) := by
  let Q : Finset (Fin (4*k+6+1)) := p1SidePacketOmitOld k v
  have hmem : ∀ i : Fin (4*k+6),
      ((v.castSucc : Fin (4*k+6+1)).succAbove i) ∈ Q := by
    intro i
    change (v.castSucc.succAbove i) ∈
      ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc)
    exact Finset.mem_erase.mpr
      ⟨Fin.succAbove_ne _ _, Finset.mem_univ _⟩
  have hmono :
      StrictMono (fun i : Fin (4*k+6) =>
        (v.castSucc : Fin (4*k+6+1)).succAbove i) :=
    Fin.strictMono_succAbove v.castSucc
  have heq :
      (fun i : Fin (4*k+6) =>
        (v.castSucc : Fin (4*k+6+1)).succAbove i) =
        (Q.orderEmbOfFin hQ : Fin (4*k+6) → Fin (4*k+6+1)) :=
    Finset.orderEmbOfFin_unique hQ hmem hmono
  ext i
  exact (congrFun heq i).symm

end Hypertournaments
