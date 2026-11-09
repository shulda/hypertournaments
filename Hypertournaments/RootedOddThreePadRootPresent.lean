import Hypertournaments.RootedOddThreePadGeometry
import Hypertournaments.RootedOddFourPadLocalIndex
import Hypertournaments.EvenPadOrderCount

/-!
# Central local type in the root-present three-pad case

Suppose the distinguished old root occurs immediately after the
three pad vertices in an increasing packet of the rooted odd
suspension. The three pad-deletion facets have the same source sign.
Deleting the root has the same raw sign, while deleting any other
old vertex has positive raw sign (the root remains in the potential).
Therefore the normalized packet consists of four alternating entries
followed by a balanced alternating tail, and its type is central.

The theorem isolates this actual geometric case. For the eventual
canonical-root suspension the root will be the first old vertex,
so every root-present three-pad packet meets this positional
hypothesis. Proving that position implication is separate.
-/

namespace Hypertournaments

/-- The true local type is central for a three-pad packet whose
next (first old) vertex is the distinguished root. -/
theorem Hyper.rootedOddSuspension_localIndex_threePads_root_at_first_old
    (k m a : ℕ) (A : Hyper (2*k+1) (Fin a))
    (root : Fin a)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (hroot :
      f (⟨3, by omega⟩ : Fin (2*k+4)) =
        evenOldShift m a root) :
    localIndex (A.rootedOddSuspension m a root) f.toEmbedding =
      k+2 := by
  let Q : Finset (Fin (m+a)) := tupleVertices f.toEmbedding
  let F : Finset (Fin a) := evenOldProjection m a Q
  let b : Bool := A.canonicalSignTable F
  let j3 : Fin (2*k+4) := ⟨3, by omega⟩
  have hroot3 : f j3 = evenOldShift m a root := hroot
  have hrootQ : evenOldShift m a root ∈ Q := by
    rw [← hroot3]
    change f j3 ∈ tupleVertices f.toEmbedding
    exact Finset.mem_image.mpr ⟨j3, Finset.mem_univ _, rfl⟩
  have hrootF : root ∈ F := by
    simp only [F, evenOldProjection, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hrootQ
  have hpad :
      ∀ i : Fin (2*k+4), i.val < 4 →
        rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) = b := by
    intro i hi
    by_cases hpre : i.val < 3
    · have hlt : (f i).val < m := by
        apply (evenPadProjection_ordered_prefix f i).1
        rw [hthree]
        exact hpre
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
        rootedOddSuspensionSignTable m a A root
            (tupleVertices (facet f.toEmbedding i)) =
          rootedOddSuspensionSignTable m a A root (Q.erase (f i)) := by
            simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
              (tupleVertices_facet_eq_erase f.toEmbedding i)
        _ = A.canonicalSignTable F := by
          rw [← hpEq]
          exact rootedOddSignTable_erase_pad_three m a A root Q
            hthree p hpProj
    · have hi3 : i = j3 := by
        apply Fin.ext
        change i.val = 3
        omega
      subst i
      calc
        rootedOddSuspensionSignTable m a A root
            (tupleVertices (facet f.toEmbedding j3)) =
          rootedOddSuspensionSignTable m a A root
            (Q.erase (f j3)) := by
              simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
                (tupleVertices_facet_eq_erase f.toEmbedding j3)
        _ = rootedOddSuspensionSignTable m a A root
            (Q.erase (evenOldShift m a root)) := by rw [hroot3]
        _ = rootedOddPotentialSignTable A root (F.erase root) :=
          rootedOddSignTable_erase_old_three m a A root Q hthree root
        _ = A.canonicalSignTable F :=
          rootedOddPotential_erase_root A root F hrootF
  have hrest :
      ∀ i : Fin (2*k+4), 4 ≤ i.val →
        rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) = true := by
    intro i hi
    have hnot : ¬ (f i).val < m := by
      intro hp
      have hsmall := (evenPadProjection_ordered_prefix f i).2 hp
      rw [hthree] at hsmall
      omega
    have hge : m ≤ (f i).val := by omega
    obtain ⟨u, huEq⟩ :=
      (evenOldShift_mem_range_iff_ge m a (f i)).2 hge
    have hru : root ≠ u := by
      intro he
      have hfEq : f j3 = f i := by
        calc
          f j3 = evenOldShift m a root := hroot3
          _ = evenOldShift m a u := by rw [he]
          _ = f i := huEq
      have hji : j3 ≠ i := by
        intro hj
        have hv := congrArg Fin.val hj
        change (3 : ℕ) = i.val at hv
        omega
      exact hji (f.injective hfEq)
    calc
      rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) =
        rootedOddSuspensionSignTable m a A root (Q.erase (f i)) := by
          simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
            (tupleVertices_facet_eq_erase f.toEmbedding i)
      _ = rootedOddSuspensionSignTable m a A root
          (Q.erase (evenOldShift m a u)) := by rw [huEq]
      _ = rootedOddPotentialSignTable A root (F.erase u) :=
        rootedOddSignTable_erase_old_three m a A root Q hthree u
      _ = true :=
        rootedOddPotential_erase_nonroot A root F hrootF u hru
  exact localIndex_ordered_fourPad_central k
    (rootedOddSuspensionSignTable m a A root) f b hpad hrest

end Hypertournaments
