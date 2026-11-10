import Hypertournaments.OddToggleP1SidePacketRawSum
import Hypertournaments.CanonicalPacket
import Hypertournaments.OddToggleP1BooleanParity

/-!
# Actual raw facet count of p1 one-point side packets

A genuine increasing (n+1)-tuple is enumerated by the vertices of
its finite-set range. The F₂ parity of its *intrinsic* raw facet
orientations agrees with the F₂ sum of the source finite-set sign
table over all singly erased vertices. This general result holds
for any ordered-sign presentation in any arity.

For the specific p1 side packet missing old v, our preceding
finite-set calculation therefore gives the exact intrinsic
raw-facet parity as prescribed base bit plus full canonical
link-row parity at v.
-/

namespace Hypertournaments

/-- Actual raw orientation parity on an increasing packet equals
the finite-set sign-table parity on all of its deleted facets. -/
theorem p1OrderedSigns_rawFacetSum
    {n a : ℕ} (signs : Finset (Fin a) → Bool)
    (g : Fin (n+1) ↪o Fin a) :
    ((boolPacketPositiveCount
      (fun i : Fin (n+1) =>
        (Hyper.fromOrderedSigns signs).orient
          (facet g.toEmbedding i)) : ℕ) : ZMod 2) =
      ∑ v ∈ tupleVertices g.toEmbedding,
        p1BitToZMod (signs ((tupleVertices g.toEmbedding).erase v)) := by
  let F : Fin a → ZMod 2 :=
    fun v => p1BitToZMod
      (signs ((tupleVertices g.toEmbedding).erase v))
  have hfacet (i : Fin (n+1)) :
      (Hyper.fromOrderedSigns signs).orient (facet g.toEmbedding i) =
        signs ((tupleVertices g.toEmbedding).erase (g i)) := by
    calc
      (Hyper.fromOrderedSigns signs).orient (facet g.toEmbedding i) =
          signs (tupleVertices (facet g.toEmbedding i)) :=
        fromOrderedSigns_facet_increasing signs g i
      _ = signs ((tupleVertices g.toEmbedding).erase (g i)) := by
        simpa using
          (congrArg signs (tupleVertices_facet_eq_erase g.toEmbedding i))
  have hinj : Set.InjOn
      (g.toEmbedding : Fin (n+1) → Fin a)
      (↑(Finset.univ : Finset (Fin (n+1)))) := by
    intro i _ j _ heq
    exact g.injective heq
  have hsum :
      (∑ v ∈ tupleVertices g.toEmbedding, F v) =
        ∑ i : Fin (n+1), F (g i) := by
    simpa [tupleVertices] using
      (Finset.sum_image
        (s := (Finset.univ : Finset (Fin (n+1))))
        (g := (g.toEmbedding : Fin (n+1) → Fin a))
        (f := F) hinj)
  calc
    ((boolPacketPositiveCount
      (fun i : Fin (n+1) =>
        (Hyper.fromOrderedSigns signs).orient
          (facet g.toEmbedding i)) : ℕ) : ZMod 2) =
        ∑ i : Fin (n+1),
          p1BitToZMod ((Hyper.fromOrderedSigns signs).orient
            (facet g.toEmbedding i)) :=
      p1BoolPacketPositiveCount_toZMod _
    _ = ∑ i : Fin (n+1), F (g i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg p1BitToZMod (hfacet i)
    _ = ∑ v ∈ tupleVertices g.toEmbedding, F v := hsum.symm

/-- The unique side packet missing old vertex v has exactly
4k+6 vertices, the local packet length for arity n=4k+5. -/
theorem p1SidePacketOmitOld_card
    (k : ℕ) (v : Fin (4*k+6)) :
    (p1SidePacketOmitOld k v).card = 4*k+6 := by
  have h := Finset.card_erase_add_one
    (Finset.mem_univ (v.castSucc : Fin (4*k+6+1)))
  change (Finset.univ.erase (v.castSucc : Fin (4*k+6+1))).card
    = 4*k+6
  have hh :
      (Finset.univ.erase (v.castSucc : Fin (4*k+6+1))).card + 1 =
        4*k+6+1 := by
    simpa using h
  omega

/-- Intrinsic full raw facet parity for *any* increasing presentation
of a genuine side packet omitting old v. -/
theorem p1SidePacket_intrinsic_rawFacetCount
    (k : ℕ) (left : Bool) (v : Fin (4*k+6))
    (g : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (hg : tupleVertices g.toEmbedding = p1SidePacketOmitOld k v) :
    ((boolPacketPositiveCount
      (fun i : Fin (4*k+6) =>
        (p1SideHyper k left).orient (facet g.toEmbedding i)) : ℕ)
          : ZMod 2) =
      p1BitToZMod (p1BaseVertexBit k v) +
        ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) := by
  have hbase := p1OrderedSigns_rawFacetSum
    (p1SideSignTable k left) g
  change
    ((boolPacketPositiveCount
      (fun i : Fin (4*k+6) =>
        (p1SideHyper k left).orient (facet g.toEmbedding i)) : ℕ)
          : ZMod 2) =
      ∑ x ∈ tupleVertices g.toEmbedding,
        p1BitToZMod
          (p1SideSignTable k left ((tupleVertices g.toEmbedding).erase x))
    at hbase
  rw [hg] at hbase
  calc
    ((boolPacketPositiveCount
      (fun i : Fin (4*k+6) =>
        (p1SideHyper k left).orient (facet g.toEmbedding i)) : ℕ)
          : ZMod 2) =
        (∑ x ∈ p1SidePacketOmitOld k v,
          p1BitToZMod (p1SideSignTable k left
            ((p1SidePacketOmitOld k v).erase x))) := hbase
    _ = p1BitToZMod (p1BaseVertexBit k v) +
          ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) :=
      p1SidePacket_rawSign_sum k left v

end Hypertournaments
