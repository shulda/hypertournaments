import Hypertournaments.OddToggleP3ActualParentEndpointFacets
import Hypertournaments.OddToggleP3CoordinateSortedOrder

/-!
# Actual increasing selected parent packet with exact deletion positions

For each selected real full block-transversal Q, the canonical
joint parent P=Q∪{l,r} has exactly m+2 vertices. Here we
construct an explicit STRICTLY INCREASING enumeration indexed
by Fin((m+1)+1). Its initial m coordinates are exactly the
real old block-coordinate vertices in increasing block order,
and its final two coordinates are the canonical left and
right fresh vertices.

This is the exact ordered-tuple interface for the remaining
raw alternating local packet argument, which previously only
had unordered finite-set facet identities. There is no order
relation in the hypertournament language; Fin is only a
canonical presentation device.
-/

namespace Hypertournaments

/-- Appending a strict upper bound to a strictly increasing
finite tuple keeps it strictly increasing. -/
theorem p3StrictMono_snoc
    {n : ℕ} {A : Type*} [LinearOrder A]
    (f : Fin n → A) (a : A)
    (hf : StrictMono f) (ha : ∀ i : Fin n, f i < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  rcases i.eq_castSucc_or_eq_last with ⟨ii,rfl⟩ | rfl
  · rcases j.eq_castSucc_or_eq_last with ⟨jj,rfl⟩ | rfl
    · have hidx : ii < jj := by
        apply Fin.lt_def.mpr
        simpa using (Fin.lt_def.mp hij)
      simpa only [Fin.snoc_castSucc] using hf hidx
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using ha ii
  · have hle : j ≤ Fin.last n := Fin.le_last j
    exact False.elim ((not_lt_of_ge hle) hij)

/-- Every genuine selected p3 parent packet has a strictly
increasing REAL vertex enumeration, with its old i-th vertex
in position i, then the left new vertex, then the right new
vertex. The finite vertex SET is exactly the constructed parent. -/
theorem p3ActualSelectedParent_increasing_tuple
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    ∃ f : Fin (((4*k+2)+1)+1) ↪o Fin (((4*k+2)*t)+2),
      tupleVertices f.toEmbedding =
        p3ActualSelectedParentSet k t ht q ∧
      (∀ i : Fin (4*k+2),
        f (i.castSucc.castSucc) =
          ((onePointBaseEmbedding ((4*k+2)*t)).trans
            (leftJointInclusion ((4*k+2)*t)))
            (p3BlockCoordinateVertex (4*k+2) t ht i (q.1 i))) ∧
      f ((Fin.last (4*k+2)).castSucc) =
        ((Fin.last ((4*k+2)*t)).castSucc) ∧
      f (Fin.last ((4*k+2)+1)) =
        Fin.last (((4*k+2)*t)+1) := by
  classical
  let m : ℕ := 4*k+2
  let a : ℕ := m*t
  let Q : Finset (Fin a) :=
    p3CoordinateTransversal m t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  let P : Finset (Fin (a+2)) :=
    p3ActualSelectedParentSet k t ht q
  let fOld : Fin m → Fin (a+2) :=
    fun i => old (p3BlockCoordinateVertex m t ht i (q.1 i))
  have hOldMono : StrictMono fOld := by
    intro i j hij
    change
      (p3BlockCoordinateVertex m t ht i (q.1 i)).castSucc.castSucc <
      (p3BlockCoordinateVertex m t ht j (q.1 j)).castSucc.castSucc
    apply (Fin.castSuccOrderEmb : Fin (a+1) ↪o Fin (a+2)).strictMono
    apply (Fin.castSuccOrderEmb : Fin a ↪o Fin (a+1)).strictMono
    exact p3BlockCoordinateVertex_strictMono m t ht q.1 hij
  have hBelowL : ∀ i : Fin m, fOld i < l := by
    intro i
    change
      (p3BlockCoordinateVertex m t ht i (q.1 i)).castSucc.castSucc <
      (Fin.last a).castSucc
    apply (Fin.castSuccOrderEmb : Fin (a+1) ↪o Fin (a+2)).strictMono
    exact Fin.castSucc_lt_last _
  have hMonoL : StrictMono (Fin.snoc fOld l) :=
    p3StrictMono_snoc fOld l hOldMono hBelowL
  have hBelowR : ∀ j : Fin (m+1),
      (Fin.snoc fOld l : Fin (m+1) → Fin (a+2)) j < r := by
    intro j
    rcases j.eq_castSucc_or_eq_last with ⟨i,rfl⟩ | rfl
    · have hi : fOld i < r := by
        change
          (p3BlockCoordinateVertex m t ht i (q.1 i)).castSucc.castSucc <
            Fin.last (a+1)
        exact Fin.castSucc_lt_last _
      simpa only [Fin.snoc_castSucc] using hi
    · have hl : l < r := by
        change (Fin.last a).castSucc < Fin.last (a+1)
        exact Fin.castSucc_lt_last _
      simpa only [Fin.snoc_last] using hl
  let F : Fin ((m+1)+1) → Fin (a+2) :=
    Fin.snoc (Fin.snoc fOld l) r
  have hMono : StrictMono F :=
    p3StrictMono_snoc (Fin.snoc fOld l) r hMonoL hBelowR
  have hMem (j : Fin ((m+1)+1)) : F j ∈ P := by
    rcases j.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
    · rcases j.eq_castSucc_or_eq_last with ⟨i,rfl⟩ | rfl
      · simp only [F, Fin.snoc_castSucc]
        change fOld i ∈ insert l (insert r (Q.image old))
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨p3BlockCoordinateVertex m t ht i (q.1 i), ?_, rfl⟩
        change p3BlockCoordinateVertex m t ht i (q.1 i) ∈
          (Finset.univ : Finset (Fin m)).image
            (fun j => p3BlockCoordinateVertex m t ht j (q.1 j))
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      · simp only [F, Fin.snoc_castSucc, Fin.snoc_last]
        change l ∈ insert l (insert r (Q.image old))
        exact Finset.mem_insert_self _ _
    · simp only [F, Fin.snoc_last]
      change r ∈ insert l (insert r (Q.image old))
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  let f : Fin ((m+1)+1) ↪o Fin (a+2) :=
    OrderEmbedding.ofStrictMono F hMono
  have hCardP : P.card = ((m+1)+1) := by
    have h := p3ActualSelectedParentSet_card k t ht q
    change P.card = 4*k+4 at h
    dsimp only [m]
    omega
  have hCardImage : (tupleVertices f.toEmbedding).card = ((m+1)+1) := by
    dsimp [tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hRange : tupleVertices f.toEmbedding = P := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact hMem j
    · rw [hCardP,hCardImage]
  refine ⟨f, hRange, ?_, ?_, ?_⟩
  · intro i
    change F i.castSucc.castSucc =
      old (p3BlockCoordinateVertex m t ht i (q.1 i))
    simp only [F,Fin.snoc_castSucc]
    rfl
  · change F ((Fin.last m).castSucc) = l
    simp only [F,Fin.snoc_castSucc,Fin.snoc_last]
  · change F (Fin.last (m+1)) = r
    simp only [F,Fin.snoc_last]

end Hypertournaments
