import Hypertournaments.CanonicalPacket

/-!
# Exact increasing enumeration after adjoining two last vertices

For an arbitrary finite old subset Q of Fin a with exactly m
vertices, append the two genuinely new vertices a and a+1 in
Fin (a+2). The increasing order of the resulting (m+2)-set is
LITERALLY the increasing old Q-enumeration followed by a and a+1.

This generic finite-order theorem supplies the last parent
packet index/order bridge for p3 negative AP. It needs no
random source assignment, potential, or hypertournament.
-/

namespace Hypertournaments

/-- The true old subset plus two greatest new vertices. -/
def p3TwoLastParentSet (a : ℕ) (Q : Finset (Fin a)) :
    Finset (Fin (a+2)) :=
  insert ((Fin.last a).castSucc)
    (insert (Fin.last (a+1))
      (Q.image (fun v : Fin a => v.castSucc.castSucc)))

/-- Explicit expected increasing enumeration of a parent with
two fresh largest vertices. -/
noncomputable def p3TwoLastIndexPoint
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m)
    (j : Fin (m+2)) : Fin (a+2) :=
  if h : j.val < m then
    ((Q.orderEmbOfFin hQ) (⟨j.val,h⟩ : Fin m)).castSucc.castSucc
  else if j.val = m then
    ((Fin.last a).castSucc : Fin (a+2))
  else Fin.last (a+1)

/-- The explicit old-then-two-fresh increasing word coincides
with the canonical increasing enumeration of the parent set. -/
theorem p3TwoLastIndexPoint_eq_orderEmbOfFin
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m)
    (hP : (p3TwoLastParentSet a Q).card = m+2) :
    p3TwoLastIndexPoint a m Q hQ =
      (p3TwoLastParentSet a Q).orderEmbOfFin hP := by
  classical
  let P := p3TwoLastParentSet a Q
  let f : Fin (m+2) → Fin (a+2) := p3TwoLastIndexPoint a m Q hQ
  have hmono : StrictMono f := by
    intro i j hij
    have hijval : i.val < j.val := hij
    change p3TwoLastIndexPoint a m Q hQ i <
      p3TwoLastIndexPoint a m Q hQ j
    unfold p3TwoLastIndexPoint
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · simp only [dif_pos hi, dif_pos hj]
        apply Fin.lt_def.mpr
        have hq := (Q.orderEmbOfFin hQ).strictMono
          (Fin.lt_def.mpr hijval :
            (⟨i.val,hi⟩ : Fin m) < (⟨j.val,hj⟩ : Fin m))
        exact Fin.lt_def.mp hq
      · by_cases hjm : j.val = m
        · simp only [dif_pos hi, dif_neg hj, if_pos hjm]
          apply Fin.lt_def.mpr
          exact (Q.orderEmbOfFin hQ (⟨i.val,hi⟩ : Fin m)).isLt
        · simp only [dif_pos hi, dif_neg hj, if_neg hjm]
          apply Fin.lt_def.mpr
          have hb := (Q.orderEmbOfFin hQ (⟨i.val,hi⟩ : Fin m)).isLt
          omega
    · have hj : ¬j.val < m := by omega
      have hieq : i.val = m := by omega
      have hjne : j.val ≠ m := by omega
      simp only [dif_neg hi, dif_neg hj, if_pos hieq, if_neg hjne]
      exact Fin.lt_def.mpr (Nat.lt_succ_self a)
  have hmem : ∀ i : Fin (m+2), f i ∈ P := by
    intro i
    change p3TwoLastIndexPoint a m Q hQ i ∈ p3TwoLastParentSet a Q
    unfold p3TwoLastIndexPoint p3TwoLastParentSet
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr
        ⟨Q.orderEmbOfFin hQ (⟨i.val,hi⟩ : Fin m),
          Finset.orderEmbOfFin_mem Q hQ _, rfl⟩
    · by_cases hieq : i.val = m
      · simp only [dif_neg hi, if_pos hieq]
        exact Finset.mem_insert_self _ _
      · simp only [dif_neg hi, if_neg hieq]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  exact Finset.orderEmbOfFin_unique hP hmem hmono

/-- Every actual old vertex occupies its old increasing index
even after adjoining two new largest vertices. -/
theorem p3TwoLast_orderEmbOfFin_old
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m)
    (hP : (p3TwoLastParentSet a Q).card = m+2)
    (i : Fin m) :
    ((p3TwoLastParentSet a Q).orderEmbOfFin hP) i.castSucc.castSucc =
      ((Q.orderEmbOfFin hQ) i).castSucc.castSucc := by
  have hEq := congrFun
    (p3TwoLastIndexPoint_eq_orderEmbOfFin a m Q hQ hP)
    (i.castSucc.castSucc)
  have hi : (i.castSucc.castSucc : Fin (m+2)).val < m := i.isLt
  simpa only [p3TwoLastIndexPoint, dif_pos hi] using hEq.symm

/-- The next-to-last parent index is the left new vertex a. -/
theorem p3TwoLast_orderEmbOfFin_left
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m)
    (hP : (p3TwoLastParentSet a Q).card = m+2) :
    ((p3TwoLastParentSet a Q).orderEmbOfFin hP)
        ((Fin.last m).castSucc) =
      (Fin.last a).castSucc := by
  have hEq := congrFun
    (p3TwoLastIndexPoint_eq_orderEmbOfFin a m Q hQ hP)
    ((Fin.last m).castSucc)
  have hn : ¬((Fin.last m).castSucc : Fin (m+2)).val < m := by
    simp
  have he : ((Fin.last m).castSucc : Fin (m+2)).val = m := rfl
  simpa only [p3TwoLastIndexPoint, dif_neg hn, if_pos he] using hEq.symm

/-- The final parent index is the right new vertex a+1. -/
theorem p3TwoLast_orderEmbOfFin_right
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m)
    (hP : (p3TwoLastParentSet a Q).card = m+2) :
    ((p3TwoLastParentSet a Q).orderEmbOfFin hP)
      (Fin.last (m+1)) = Fin.last (a+1) := by
  have hEq := congrFun
    (p3TwoLastIndexPoint_eq_orderEmbOfFin a m Q hQ hP)
    (Fin.last (m+1))
  have hn : ¬(Fin.last (m+1) : Fin (m+2)).val < m := by simp
  have he : (Fin.last (m+1) : Fin (m+2)).val ≠ m := by omega
  simpa only [p3TwoLastIndexPoint, dif_neg hn, if_neg he] using hEq.symm

end Hypertournaments
