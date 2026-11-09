import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.RootedOddFourPadCount
import Hypertournaments.EvenSuspensionTwoThreeFacets
import Hypertournaments.EvenPadOrderCount
import Hypertournaments.CanonicalPacket
import Hypertournaments.UniformPacketPermutationCount

/-!
# Four-pad centrality for the actual rooted odd suspension

For odd source arity 2k+1, an increasing (2k+4)-vertex packet
containing exactly four pads has equal raw signs on its four
pad-deletion facets, each reading the old root potential, and
positive raw signs on all remaining facets. Its normalized packet
has a central minority index k+2.

This module proves the exact finite-set facet geometry, the uniform
normalized Boolean packet calculation, and their application to
the genuine intrinsic rooted suspension on the canonical increasing
packet. No AP assumption or unproved class membership is introduced.
-/

namespace Hypertournaments

/-- Erasing a present pad from a four-pad packet leaves exactly
three pads, and the old projection is unchanged. -/
theorem rootedOddSignTable_erase_pad_four
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a)) (root : Fin a)
    (Q : Finset (Fin (m+a)))
    (hfour : (evenPadProjection m a Q).card = 4)
    (p : Fin m) (hp : p ∈ evenPadProjection m a Q) :
    rootedOddSuspensionSignTable m a A root
        (Q.erase (evenPadShift m a p)) =
      rootedOddPotentialSignTable A root (evenOldProjection m a Q) := by
  have hthree :
      (evenPadProjection m a
        (Q.erase (evenPadShift m a p))).card = 3 := by
    rw [evenPadProjection_erase_pad]
    have hh := Finset.card_erase_add_one hp
    omega
  rw [rootedOddSuspensionSignTable_threePads m a A root _ hthree]
  rw [evenOldProjection_erase_pad]

/-- Erasing any nonpad from a four-pad packet leaves four pads,
hence the suspended raw sign is positive. -/
theorem rootedOddSignTable_erase_nonpad_four
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a)) (root : Fin a)
    (Q : Finset (Fin (m+a)))
    (hfour : (evenPadProjection m a Q).card = 4)
    (v : Fin (m+a)) (hv : v ∉ Set.range (evenPadShift m a)) :
    rootedOddSuspensionSignTable m a A root (Q.erase v) = true := by
  have hcard :
      (evenPadProjection m a (Q.erase v)).card = 4 := by
    rw [evenPadProjection_erase_nonpad m a Q v hv]
    exact hfour
  unfold rootedOddSuspensionSignTable
  simp [hcard]

/-- The complementary length-2k alternating vector has exactly
k positive entries, just like the original alternating vector. -/
theorem boolPacketPositiveCount_alternating_even_complement (k : ℕ) :
    boolPacketPositiveCount
      (fun i : Fin (2*k) => decide (i.val%2=0)) = k := by
  have hb :
      (fun i : Fin (2*k) => decide (i.val%2=0)) =
      (fun i : Fin (2*k) => !(decide (i.val%2=1))) := by
    funext i
    by_cases hi : i.val % 2 = 1
    · have hn : i.val % 2 ≠ 0 := by omega
      simp [hi, hn]
    · have hz : i.val % 2 = 0 := by omega
      simp [hi, hz]
  rw [hb, boolPacketPositiveCount_not, boolPacketPositiveCount_alternating_even]
  omega

/-- A genuine intrinsic (2k+3)-hypertournament packet with its
first four raw facet signs equal to b and all remaining signs
positive has local central type k+2, on increasing tuples. -/
theorem localIndex_ordered_fourPad_central
    (k : ℕ) {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin (2*k+4) ↪o V)
    (b : Bool)
    (hpad : ∀ i : Fin (2*k+4), i.val < 4 →
      signs (tupleVertices (facet f.toEmbedding i)) = b)
    (hold : ∀ i : Fin (2*k+4), 4 ≤ i.val →
      signs (tupleVertices (facet f.toEmbedding i)) = true) :
    localIndex (Hyper.fromOrderedSigns (n := 2*k+3) signs)
      f.toEmbedding = k+2 := by
  let D : Hyper (2*k+3) V := Hyper.fromOrderedSigns signs
  have hraw (i : Fin (2*k+4)) :
      D.orient (facet f.toEmbedding i) =
        signs (tupleVertices (facet f.toEmbedding i)) :=
    fromOrderedSigns_facet_increasing signs f i
  have h0 :
      normalizedFacet D f.toEmbedding (0 : Fin (2*k+4)) = b := by
    unfold normalizedFacet
    rw [hraw 0, hpad 0 (by simp only [Fin.val_zero]; omega)]
    simp
  have h1 :
      normalizedFacet D f.toEmbedding
        ((0 : Fin (2*k+3)).succ) = !b := by
    unfold normalizedFacet
    rw [hraw _, hpad _ (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
    cases b <;> simp [Fin.val_succ, Fin.val_zero]
  have h2 :
      normalizedFacet D f.toEmbedding
        ((0 : Fin (2*k+2)).succ.succ) = b := by
    unfold normalizedFacet
    rw [hraw _, hpad _ (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
    change (b ^^ decide ((2 % (2*k+3+1)) % 2 = 1)) = b
    have hlt : 2 < 2*k+3+1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    simp
  have h3 :
      normalizedFacet D f.toEmbedding
        ((0 : Fin (2*k+1)).succ.succ.succ) = !b := by
    unfold normalizedFacet
    rw [hraw _, hpad _ (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
    change (b ^^ decide ((3 % (2*k+3+1)) % 2 = 1)) = !b
    have hlt : 3 < 2*k+3+1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    cases b <;> decide
  have htail (j : Fin (2*k)) :
      normalizedFacet D f.toEmbedding j.succ.succ.succ.succ =
        decide (j.val%2=0) := by
    have hpos : D.orient (facet f.toEmbedding j.succ.succ.succ.succ) =
      true := (hraw _).trans (hold _ (by
        simp only [Fin.val_succ]
        omega))
    unfold normalizedFacet
    rw [hpos]
    simp only [Fin.val_succ]
    by_cases hj : j.val % 2 = 1
    · have hnew : (j.val+1+1+1+1)%2 = 1 := by omega
      have hn : j.val % 2 ≠ 0 := by omega
      simp [hj,hnew,hn]
    · have hnew : (j.val+1+1+1+1)%2 ≠ 1 := by omega
      have hz : j.val % 2 = 0 := by omega
      simp [hj,hnew,hz]
  have hbits :
      (fun i : Fin (2*k+4) => normalizedFacet D f.toEmbedding i) =
        Fin.cons b (Fin.cons (!b) (Fin.cons b (Fin.cons (!b)
          (fun j : Fin (2*k) => decide (j.val%2=0))))) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_
      (fun j => Fin.cases ?_ (fun q => Fin.cases ?_
        (fun t => ?_) q) j) i) i
    · simpa only [Fin.cons_zero] using h0
    · simpa only [Fin.cons_succ, Fin.cons_zero] using h1
    · simpa only [Fin.cons_succ, Fin.cons_zero] using h2
    · simpa only [Fin.cons_succ, Fin.cons_zero] using h3
    · simpa only [Fin.cons_succ] using htail t
  change
    min (boolPacketPositiveCount
        (fun i : Fin (2*k+4) => normalizedFacet D f.toEmbedding i))
      ((2*k+4)-boolPacketPositiveCount
        (fun i : Fin (2*k+4) => normalizedFacet D f.toEmbedding i))
      = k+2
  rw [hbits]
  exact boolPacketMinority_four_pad_central k b
    (fun j : Fin (2*k) => decide (j.val%2=0))
    (boolPacketPositiveCount_alternating_even_complement k)

/-- The concrete rooted odd suspension has central type on every
increasing local packet containing exactly four auxiliary pads. -/
theorem Hyper.rootedOddSuspension_localIndex_increasing_fourPads
    (k m a : ℕ) (A : Hyper (2*k+1) (Fin a))
    (root : Fin a)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hfour :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 4) :
    localIndex (A.rootedOddSuspension m a root) f.toEmbedding = k+2 := by
  let Q : Finset (Fin (m+a)) := tupleVertices f.toEmbedding
  let b : Bool := rootedOddPotentialSignTable A root (evenOldProjection m a Q)
  have hpad :
      ∀ i : Fin (2*k+4), i.val < 4 →
        rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) = b := by
    intro i hi
    have hlt : (f i).val < m := by
      apply (evenPadProjection_ordered_prefix f i).1
      rw [hfour]
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
      rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) =
        rootedOddSuspensionSignTable m a A root (Q.erase (f i)) := by
          simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
            (tupleVertices_facet_eq_erase f.toEmbedding i)
      _ = rootedOddPotentialSignTable A root (evenOldProjection m a Q) := by
        rw [← hpEq]
        exact rootedOddSignTable_erase_pad_four m a A root Q hfour p hpProj
  have hold :
      ∀ i : Fin (2*k+4), 4 ≤ i.val →
        rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) = true := by
    intro i hi
    have hnot : ¬(f i).val < m := by
      intro hp
      have hsmall := (evenPadProjection_ordered_prefix f i).2 hp
      rw [hfour] at hsmall
      omega
    have hv : f i ∉ Set.range (evenPadShift m a) := by
      intro h
      exact hnot ((evenPadShift_mem_range_iff_lt m a (f i)).1 h)
    calc
      rootedOddSuspensionSignTable m a A root
          (tupleVertices (facet f.toEmbedding i)) =
        rootedOddSuspensionSignTable m a A root (Q.erase (f i)) := by
          simpa [Q] using congrArg (rootedOddSuspensionSignTable m a A root)
            (tupleVertices_facet_eq_erase f.toEmbedding i)
      _ = true := rootedOddSignTable_erase_nonpad_four m a A root Q hfour (f i) hv
  exact localIndex_ordered_fourPad_central k
    (rootedOddSuspensionSignTable m a A root) f b hpad hold

end Hypertournaments
