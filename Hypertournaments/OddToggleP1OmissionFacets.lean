import Hypertournaments.OddToggleP1MissingSets
import Hypertournaments.OddToggleP1ExplicitSides

/-!
# Exact facets of a p1 side packet omitting one old vertex

The actual one-point sides have vertex set Fin(4k+7), with their
new vertex last. Every (n+1)-subset involving the new vertex
is the full side vertex set with exactly one old base point omitted.

Deleting the new point from this side packet gives the base sign
at the omitted old vertex. Deleting a second old vertex gives the
canonical pair-link sign of the two omitted old vertices.

These are literal finite-set identities on the true source sign
tables. They do not assume any AP, admissibility or precomputed local
type, and are the interface for the row-parity side proof.
-/

namespace Hypertournaments

/-- An actual (n+1)-element side packet formed by omitting one
old base vertex from the full side universe. -/
def p1SidePacketOmitOld (k : ℕ) (v : Fin (4*k+6)) :
    Finset (Fin (4*k+6+1)) :=
  (Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc

/-- All base vertices except v remain in this side packet. -/
theorem p1SidePacketOmitOld_mem_old (k : ℕ)
    (v w : Fin (4*k+6)) :
    (w.castSucc : Fin (4*k+6+1)) ∈ p1SidePacketOmitOld k v ↔
      w ≠ v := by
  simp only [p1SidePacketOmitOld, Finset.mem_erase,
    Finset.mem_univ, and_true]
  constructor
  · intro h
    intro he
    subst w
    exact h rfl
  · intro h
    intro he
    exact h ((Fin.castSuccEmb : Fin (4*k+6) ↪
      Fin (4*k+6+1)).injective he)

/-- The distinguished side packet includes the new last vertex. -/
theorem p1SidePacketOmitOld_last (k : ℕ)
    (v : Fin (4*k+6)) :
    Fin.last (4*k+6) ∈ p1SidePacketOmitOld k v := by
  change Fin.last (4*k+6) ≠ v.castSucc ∧ True
  constructor
  · intro he
    have hval := congrArg Fin.val he
    have hv := v.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hval
    omega
  · trivial

/-- Omitting old v and then old w leaves exactly those two
old base vertices missing, independently of their order. -/
theorem p1SidePacket_missing_two_old (k : ℕ)
    (v w : Fin (4*k+6)) :
    p1MissingBase k ((p1SidePacketOmitOld k v).erase w.castSucc) =
      ({v,w} : Finset (Fin (4*k+6))) := by
  ext x
  have hv :
      (x.castSucc : Fin (4*k+6+1)) = v.castSucc ↔ x = v := by
    constructor
    · exact (Fin.castSuccEmb : Fin (4*k+6) ↪
        Fin (4*k+6+1)).injective
    · intro h
      rw [h]
  have hw :
      (x.castSucc : Fin (4*k+6+1)) = w.castSucc ↔ x = w := by
    constructor
    · exact (Fin.castSuccEmb : Fin (4*k+6) ↪
        Fin (4*k+6+1)).injective
    · intro h
      rw [h]
  change ((x.castSucc : Fin (4*k+6+1)) ∉
    ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc).erase
      w.castSucc) ↔ x ∈ ({v,w} : Finset (Fin (4*k+6)))
  simp only [Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_insert, Finset.mem_singleton]
  simp only [not_and_or, not_not]
  rw [hw, hv]
  tauto

/-- Omitting old v and then the new endpoint leaves exactly
v missing from the old base part. -/
theorem p1SidePacket_missing_old_new (k : ℕ)
    (v : Fin (4*k+6)) :
    p1MissingBase k
      ((p1SidePacketOmitOld k v).erase (Fin.last (4*k+6))) =
      ({v} : Finset (Fin (4*k+6))) := by
  ext x
  have hv :
      (x.castSucc : Fin (4*k+6+1)) = v.castSucc ↔ x = v := by
    constructor
    · exact (Fin.castSuccEmb : Fin (4*k+6) ↪
        Fin (4*k+6+1)).injective
    · intro h
      rw [h]
  have hlast :
      (x.castSucc : Fin (4*k+6+1)) ≠ Fin.last (4*k+6) := by
    intro he
    have hvx := x.isLt
    have hval := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_last] at hval
    omega
  change ((x.castSucc : Fin (4*k+6+1)) ∉
    ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc).erase
      (Fin.last (4*k+6))) ↔
    x ∈ ({v} : Finset (Fin (4*k+6)))
  simp only [Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_singleton]
  simp only [not_and_or, not_not]
  simp [hlast, hv]

/-- The raw sign on the facet deleting the new vertex from a
side packet omitting old v is the prescribed common-base bit b_v. -/
theorem p1SidePacket_sign_erase_new (k : ℕ)
    (left : Bool) (v : Fin (4*k+6)) :
    p1SideSignTable k left
      ((p1SidePacketOmitOld k v).erase (Fin.last (4*k+6))) =
        p1BaseVertexBit k v := by
  have hend :
      Fin.last (4*k+6) ∉
        (p1SidePacketOmitOld k v).erase (Fin.last (4*k+6)) := by simp
  have hmissing := p1SidePacket_missing_old_new k v
  unfold p1SideSignTable
  rw [if_neg hend, hmissing]
  exact p1BaseMissingBit_singleton k v

/-- The raw sign on the facet deleting a second distinct old
vertex w, when v<w, is the prescribed canonical pair link v,w. -/
theorem p1SidePacket_sign_erase_old (k : ℕ)
    (left : Bool) (v w : Fin (4*k+6)) (hvw : v < w) :
    p1SideSignTable k left
      ((p1SidePacketOmitOld k v).erase w.castSucc) =
        p1CanonicalLink k left v w := by
  have hend :
      Fin.last (4*k+6) ∈
        (p1SidePacketOmitOld k v).erase w.castSucc := by
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have hwval := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_castSucc] at hwval
      have hwlt := w.isLt
      omega
    · exact p1SidePacketOmitOld_last k v
  have hmissing := p1SidePacket_missing_two_old k v w
  unfold p1SideSignTable
  rw [if_pos hend, hmissing]
  exact p1PairMissingBit_pair k left v w hvw

end Hypertournaments
