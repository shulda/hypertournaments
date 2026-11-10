import Hypertournaments.OddToggleP1ActualRawCount
import Hypertournaments.OddToggleP1EvenRawAllowed

/-!
# Full intrinsic even-raw admissibility from a matching link-row parity

The actual side packet missing old vertex v has F₂ raw orientation
sum b_v + row(v). If row(v) has the same mod-two value as b_v,
the full raw facet word has even positive count. Consequently
the true intrinsic local type is allowed in the p1 exceptional
toggle-zero family, without computing every orientation orbit.

This lemma is uniform in k, side, and v. The remaining side-age
proof need only supply matching row parities except at the two
protected right-hand core vertices, where the type is homogeneous.
-/

namespace Hypertournaments

theorem p1NatEven_ofZMod2_zero (r : ℕ)
    (h : (r : ZMod 2) = 0) :
    r % 2 = 0 := by
  by_contra hn
  have ho : r % 2 = 1 := by omega
  have hOne : (r : ZMod 2) = 1 := by
    rw [p1NatCast_eq_oddBit]
    simp [ho, p1BitToZMod]
  exact (by decide : (1 : ZMod 2) ≠ 0) (hOne.symm.trans h)

/-- If the canonical link-row parity agrees with the omitted
base vertex bit, the actual side packet has even raw orientation
count on any increasing enumeration of its genuine finite set. -/
theorem p1SidePacket_rawEven_of_rowParity
    (k : ℕ) (left : Bool) (v : Fin (4*k+6))
    (g : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (hg : tupleVertices g.toEmbedding = p1SidePacketOmitOld k v)
    (hrow : p1CanonicalRowPositiveCount k left v % 2 =
      (if p1BaseVertexBit k v then 1 else 0)) :
    boolPacketPositiveCount
      (fun i : Fin (4*k+6) =>
        (p1SideHyper k left).orient (facet g.toEmbedding i)) % 2 = 0 := by
  have hrowz :
      ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) =
        p1BitToZMod (p1BaseVertexBit k v) := by
    rw [p1NatCast_eq_oddBit]
    cases hb : p1BaseVertexBit k v <;>
      simp [hb, hrow, p1BitToZMod] at *
  have hrawz :
      ((boolPacketPositiveCount
        (fun i : Fin (4*k+6) =>
          (p1SideHyper k left).orient (facet g.toEmbedding i)) : ℕ)
        : ZMod 2) = 0 := by
    calc
      _ = p1BitToZMod (p1BaseVertexBit k v) +
          ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) :=
        p1SidePacket_intrinsic_rawFacetCount k left v g hg
      _ = p1BitToZMod (p1BaseVertexBit k v) +
            p1BitToZMod (p1BaseVertexBit k v) := by rw [hrowz]
      _ = 0 := by
        cases hb : p1BaseVertexBit k v <;>
          decide
  exact p1NatEven_ofZMod2_zero _ hrawz

/-- The matching link-row parity certifies actual p1 local
admissibility of the side packet, without any global age assumption. -/
theorem p1SidePacket_allowed_of_rowParity
    (k : ℕ) (left : Bool) (v : Fin (4*k+6))
    (g : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (hg : tupleVertices g.toEmbedding = p1SidePacketOmitOld k v)
    (hrow : p1CanonicalRowPositiveCount k left v % 2 =
      (if p1BaseVertexBit k v then 1 else 0)) :
    localIndex (p1SideHyper k left) g.toEmbedding ∈
      toggleZero (switchingAllowed (4*k+5)) := by
  exact (p1SideHyper k left).p1Toggle_allowed_of_even_rawFacetCount
    k g.toEmbedding
      (p1SidePacket_rawEven_of_rowParity k left v g hg hrow)

end Hypertournaments
