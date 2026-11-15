import Hypertournaments.RootedOddThreePadGeometry
import Hypertournaments.EvenPadOrderCount
import Hypertournaments.CanonicalPacket

/-!
# Actual ordered facet signs of the root-absent three-pad packet

A three-pad high packet with no distinguished old root has three
pad-deletion facets reading the source sign on its old projection.
Deleting an old coordinate reads the source sign on the old
projection with that coordinate erased and the root inserted.

This proves the *intrinsic*, ordered-orientation bridge. It makes no
claim about the source packet until a root-prefixed old increasing
tuple has been constructed. The next lemma can compare normalized
facets coordinate-by-coordinate using these exact two cases.
-/

namespace Hypertournaments

/-- For a genuine increasing three-pad packet of the concrete rooted
suspension with the root absent from the old projection, identify
all its actual raw facet orientations. -/
theorem Hyper.rootedOddSuspension_threePads_rootAbsent_rawFacets
    {n m a : ℕ} (A : Hyper n (Fin a)) (root : Fin a)
    (f : Fin (n+3) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (habsent :
      root ∉ evenOldProjection m a (tupleVertices f.toEmbedding)) :
    (∀ i : Fin (n+3), i.val < 3 →
      (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
        A.canonicalSignTable
          (evenOldProjection m a (tupleVertices f.toEmbedding))) ∧
    (∀ (j : Fin n) (u : Fin a),
      f j.succ.succ.succ = evenOldShift m a u →
      (A.rootedOddSuspension m a root).orient
          (facet f.toEmbedding j.succ.succ.succ) =
        A.canonicalSignTable
          (insert root
            ((evenOldProjection m a (tupleVertices f.toEmbedding)).erase u))) := by
  let Q : Finset (Fin (m+a)) := tupleVertices f.toEmbedding
  let F : Finset (Fin a) := evenOldProjection m a Q
  constructor
  · intro i hi
    have hlt : (f i).val < m := by
      apply (evenPadProjection_ordered_prefix f i).1
      rw [hthree]
      exact hi
    obtain ⟨p, hpEq⟩ :=
      (evenPadShift_mem_range_iff_lt m a (f i)).2 hlt
    have hpMem : evenPadShift m a p ∈ Q := by
      rw [hpEq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hpProj : p ∈ evenPadProjection m a Q := by
      simp only [evenPadProjection, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hpMem
    calc
      (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
          rootedOddSuspensionSignTable m a A root
            (tupleVertices (facet f.toEmbedding i)) :=
        fromOrderedSigns_facet_increasing
          (rootedOddSuspensionSignTable m a A root) f i
      _ = rootedOddSuspensionSignTable m a A root (Q.erase (f i)) := by
        simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
          (tupleVertices_facet_eq_erase f.toEmbedding i)
      _ = rootedOddSuspensionSignTable m a A root
          (Q.erase (evenPadShift m a p)) := by rw [hpEq]
      _ = A.canonicalSignTable F :=
        rootedOddSignTable_erase_pad_three m a A root Q hthree p hpProj
  · intro j u hj
    calc
      (A.rootedOddSuspension m a root).orient
          (facet f.toEmbedding j.succ.succ.succ) =
        rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding j.succ.succ.succ)) :=
        fromOrderedSigns_facet_increasing
          (rootedOddSuspensionSignTable m a A root) f j.succ.succ.succ
      _ = rootedOddSuspensionSignTable m a A root
          (Q.erase (f j.succ.succ.succ)) := by
        simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
          (tupleVertices_facet_eq_erase f.toEmbedding j.succ.succ.succ)
      _ = rootedOddSuspensionSignTable m a A root
          (Q.erase (evenOldShift m a u)) := by rw [hj]
      _ = rootedOddPotentialSignTable A root (F.erase u) :=
        rootedOddSignTable_erase_old_three m a A root Q hthree u
      _ = A.canonicalSignTable (insert root (F.erase u)) :=
        rootedOddPotential_erase_of_root_absent A root F habsent u

end Hypertournaments
