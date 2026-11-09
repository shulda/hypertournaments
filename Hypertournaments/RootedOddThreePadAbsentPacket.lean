import Hypertournaments.RootedOddThreePadAbsentOrderedSigns

/-!
# The actual root-absent normalized three-pad packet

On an increasing high (n+3)-packet with three pads, suppose the root
is absent from the old projection, and a source increasing (n+1)-tuple
g has that root first and then exactly the old high tail. The high
normalized packet is the old normalized packet with its first sign b
replaced by (b, !b, b). All facet signs are those of the actual
intrinsic hypertournaments; no Boolean packet is substituted by fiat.
-/

namespace Hypertournaments

/-- Identify the normalized facets coordinate by coordinate for
root-absent three-pad packets of the *concrete* rooted suspension. -/
theorem Hyper.rootedOddSuspension_threePads_rootAbsent_packetEq
    {n m a : ℕ} (A : Hyper n (Fin a)) (root : Fin a)
    (f : Fin (n+3) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (habsent :
      root ∉ evenOldProjection m a (tupleVertices f.toEmbedding))
    (g : Fin (n+1) ↪o Fin a)
    (hgRoot : g (0 : Fin (n+1)) = root)
    (hgTail : ∀ j : Fin n,
      f j.succ.succ.succ = evenOldShift m a (g j.succ))
    (hgVertices : tupleVertices g.toEmbedding =
      insert root (evenOldProjection m a (tupleVertices f.toEmbedding))) :
    (fun i : Fin (n+3) =>
      normalizedFacet (A.rootedOddSuspension m a root) f.toEmbedding i) =
      Fin.cons (normalizedFacet A g.toEmbedding 0)
        (Fin.cons (!(normalizedFacet A g.toEmbedding 0))
          (Fin.cons (normalizedFacet A g.toEmbedding 0)
            (fun j : Fin n => normalizedFacet A g.toEmbedding j.succ))) := by
  let F : Finset (Fin a) :=
    evenOldProjection m a (tupleVertices f.toEmbedding)
  have hnot : root ∉ F := habsent
  have hraw := A.rootedOddSuspension_threePads_rootAbsent_rawFacets
    root f hthree habsent
  have hsrc (i : Fin (n+1)) :
      A.orient (facet g.toEmbedding i) =
        A.canonicalSignTable (tupleVertices (facet g.toEmbedding i)) := by
    calc
      A.orient (facet g.toEmbedding i) =
          (Hyper.fromOrderedSigns A.canonicalSignTable).orient
            (facet g.toEmbedding i) :=
        (A.from_canonicalSignTable_orient (facet g.toEmbedding i)).symm
      _ = A.canonicalSignTable (tupleVertices (facet g.toEmbedding i)) :=
        fromOrderedSigns_facet_increasing A.canonicalSignTable g i
  have hgRootE : g.toEmbedding (0 : Fin (n+1)) = root := hgRoot
  have hsrc0 :
      A.orient (facet g.toEmbedding 0) = A.canonicalSignTable F := by
    rw [hsrc 0, tupleVertices_facet_eq_erase, hgVertices, hgRootE]
    simp [F, hnot]
  have hrNe (j : Fin n) : root ≠ g j.succ := by
    intro he
    have hzero : (0 : Fin (n+1)) = j.succ :=
      g.injective (hgRoot.trans he)
    have hv := congrArg Fin.val hzero
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  have hsrcTail (j : Fin n) :
      A.orient (facet g.toEmbedding j.succ) =
        A.canonicalSignTable (insert root (F.erase (g j.succ))) := by
    rw [hsrc j.succ, tupleVertices_facet_eq_erase, hgVertices]
    apply congrArg A.canonicalSignTable
    ext v
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hneq, hroot | hF⟩
      · exact Or.inl hroot
      · exact Or.inr ⟨hneq, hF⟩
    · rintro (hroot | ⟨hneq, hF⟩)
      · subst v
        exact ⟨hrNe j, Or.inl rfl⟩
      · exact ⟨hneq, Or.inr hF⟩
  have hsrc0norm :
      normalizedFacet A g.toEmbedding 0 = A.canonicalSignTable F := by
    unfold normalizedFacet
    rw [hsrc0]
    simp
  have hpad0 : ((0 : Fin (n+3)).val < 3) := by omega
  have hpad1 : (((0 : Fin (n+2)).succ : Fin (n+3)).val < 3) := by
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hpad2 : (((0 : Fin (n+1)).succ.succ : Fin (n+3)).val < 3) := by
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have h1val : (((0 : Fin (n+2)).succ : Fin (n+3)).val = 1) := by
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have h2val : (((0 : Fin (n+1)).succ.succ : Fin (n+3)).val = 2) := by
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have h0 :
      normalizedFacet (A.rootedOddSuspension m a root) f.toEmbedding
        (0 : Fin (n+3)) = normalizedFacet A g.toEmbedding 0 := by
    rw [hsrc0norm]
    unfold normalizedFacet
    rw [hraw.1 0 hpad0]
    simp [F]
  have h1 :
      normalizedFacet (A.rootedOddSuspension m a root) f.toEmbedding
        ((0 : Fin (n+2)).succ) = !(normalizedFacet A g.toEmbedding 0) := by
    rw [hsrc0norm]
    unfold normalizedFacet
    rw [hraw.1 _ hpad1]
    simp [F, h1val]
  have h2 :
      normalizedFacet (A.rootedOddSuspension m a root) f.toEmbedding
        ((0 : Fin (n+1)).succ.succ) = normalizedFacet A g.toEmbedding 0 := by
    rw [hsrc0norm]
    unfold normalizedFacet
    rw [hraw.1 _ hpad2]
    simp [F, h2val]
  have htail (j : Fin n) :
      normalizedFacet (A.rootedOddSuspension m a root) f.toEmbedding
        j.succ.succ.succ = normalizedFacet A g.toEmbedding j.succ := by
    unfold normalizedFacet
    rw [hraw.2 j (g j.succ) (hgTail j), hsrcTail j]
    have hmod : (j.val + 1 + 1 + 1) % 2 = (j.val + 1) % 2 := by omega
    simpa [F, Fin.val_succ, hmod]
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun j => Fin.cases ?_ (fun t => ?_) j) i) i
  · simpa only [Fin.cons_zero] using h0
  · simpa only [Fin.cons_succ, Fin.cons_zero] using h1
  · simpa only [Fin.cons_succ, Fin.cons_zero] using h2
  · simpa only [Fin.cons_succ] using htail t

end Hypertournaments
