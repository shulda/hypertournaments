import Hypertournaments.OddToggleP3ActualMixedBooleanSource
import Hypertournaments.OddToggleP3BasePreservation

/-!
# Literal parent packet and its actual mixed/endpoint facet sets

A selected zero-sum transversal Q gives an actual (n+1)-set
P = Q ∪ {left fresh,right fresh} in the canonical joint.
The two fresh vertices lie strictly after all old vertices.

We prove that this genuine parent packet has exactly n+1
vertices, and that erasing its old vertex in block i gives
precisely the true selected mixed n-set used by the universal
Boolean source-gauge theorem. Erasing the two fresh vertices
gives the actual respective one-point endpoint n-sets.

This is exact SET geometry. The remaining packet step is to
identify the positions in the unique increasing enumeration
with the old block indices followed by the two fresh points.
-/

namespace Hypertournaments

open scoped Classical

/-- True parent (n+1)-set selected by a zero-sum full old
transversal and the two canonical new vertices. -/
def p3ActualSelectedParentSet
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    Finset (Fin ((4*k+2)*t+2)) :=
  let a : ℕ := (4*k+2)*t
  let Q : Finset (Fin a) :=
    p3CoordinateTransversal (4*k+2) t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  insert ((Fin.last a).castSucc)
    (insert (Fin.last (a+1)) (Q.image old))

/-- Every selected actual parent packet has cardinality
(4k+3)+1, so it can be enumerated canonically as a genuine
arity-(4k+3) local packet. -/
theorem p3ActualSelectedParentSet_card
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    (p3ActualSelectedParentSet k t ht q).card = 4*k+4 := by
  classical
  let m : ℕ := 4*k+2
  let a : ℕ := m*t
  let Q : Finset (Fin a) := p3CoordinateTransversal m t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  have hQ : Q.card = m := p3CoordinateTransversal_card m t ht q.1
  have hOldCard : (Q.image old).card = m := by
    rw [Finset.card_image_of_injective _ old.injective]
    exact hQ
  have hr : r ∉ Q.image old := by
    intro hmem
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
    change v.castSucc.castSucc = Fin.last (a+1) at hv
    exact Fin.castSucc_ne_last (v.castSucc) hv
  have hlold : l ∉ Q.image old := by
    intro hmem
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
    change v.castSucc.castSucc = (Fin.last a).castSucc at hv
    have heq : v.castSucc = Fin.last a :=
      (Fin.castSuccEmb : Fin (a+1) ↪ Fin (a+2)).injective hv
    exact Fin.castSucc_ne_last v heq
  have hlr : l ≠ r := Fin.castSucc_ne_last (Fin.last a)
  have hl : l ∉ insert r (Q.image old) := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨hlr,hlold⟩
  change (insert l (insert r (Q.image old))).card = 4*k+4
  calc
    (insert l (insert r (Q.image old))).card =
        (insert r (Q.image old)).card + 1 := by simp [hl]
    _ = (Q.image old).card + 2 := by simp [hr]; omega
    _ = 4*k+4 := by omega

/-- Removing the true old vertex from block i of a selected
parent packet leaves EXACTLY the actual mixed n-set used by
the selected Boolean source/gauge formula. -/
theorem p3ActualSelectedParent_erase_old_vertex
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) :
    (p3ActualSelectedParentSet k t ht q).erase
      (((onePointBaseEmbedding ((4*k+2)*t)).trans
        (leftJointInclusion ((4*k+2)*t)))
        (p3BlockCoordinateVertex (4*k+2) t ht i (q.1 i))) =
      p3ActualSelectedMixedSet k t ht q i := by
  classical
  let m : ℕ := 4*k+2
  let a : ℕ := m*t
  let Q : Finset (Fin a) := p3CoordinateTransversal m t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  let v : Fin a := p3BlockCoordinateVertex m t ht i (q.1 i)
  have hlne : l ≠ old v := by
    intro heq
    change (Fin.last a).castSucc = v.castSucc.castSucc at heq
    have hv : Fin.last a = v.castSucc :=
      (Fin.castSuccEmb : Fin (a+1) ↪ Fin (a+2)).injective heq
    exact Fin.castSucc_ne_last v hv.symm
  have hrne : r ≠ old v := by
    intro heq
    change Fin.last (a+1) = v.castSucc.castSucc at heq
    exact Fin.castSucc_ne_last (v.castSucc) heq.symm
  change (insert l (insert r (Q.image old))).erase (old v) =
    insert l (insert r ((Q.erase v).image old))
  rw [Finset.erase_insert_of_ne hlne, Finset.erase_insert_of_ne hrne]
  rw [p3Finset_image_erase old Q v]

end Hypertournaments
