import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1SidePacketOldImage
import Hypertournaments.OddToggleP1RowCountSplit
import Hypertournaments.OddToggleP1Parity
import Hypertournaments.OddToggleP1BooleanParity
import Hypertournaments.OddToggleP1CanonicalLinkSymmetry

/-!
# Genuine p1 side packet raw sign parity from canonical link rows

Let Q be the actual (n+1)-packet in the one-point side obtained by
omitting old base vertex v. The n-facet obtained by deleting the new
last point reads the prescribed base sign b_v. The remaining facets,
indexed by all other old vertices w, read precisely link(v,w).

The F₂ sum over all actual facet signs thus equals
  b_v + (full canonical link-row positive count at v) mod 2.
There is no artificial ordered-representative assumption, and
the diagonal v-v contribution is identically false.
This is the parity accounting needed for side age membership.
-/

namespace Hypertournaments

/-- In the p1 canonical table, erasing the absent old vertex v
does not change the sum of all row indicators because the diagonal
entry is zero. -/
theorem p1CanonicalRow_sum_erase
    (k : ℕ) (left : Bool) (v : Fin (4*k+6)) :
    (∑ w ∈ ((Finset.univ : Finset (Fin (4*k+6))).erase v),
      p1BitToZMod (p1CanonicalLink k left v w)) =
        ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) := by
  let S : Finset (Fin (4*k+6)) :=
    (Finset.univ : Finset (Fin (4*k+6))).erase v
  let H : Fin (4*k+6) → Prop :=
    fun w => p1CanonicalLink k left v w = true
  have hdiag : p1CanonicalLink k left v v = false :=
    p1CanonicalLink_diagonal_false k left v
  have hfilter : S.filter H =
      (Finset.univ : Finset (Fin (4*k+6))).filter H := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [S, H, hdiag]
    · simp [S, H, hw]
  have hbit (w : Fin (4*k+6)) :
      p1BitToZMod (p1CanonicalLink k left v w) =
        (if H w then (1 : ZMod 2) else 0) := by
    dsimp [H]
    cases h : p1CanonicalLink k left v w <;>
      simp [h, p1BitToZMod]
  calc
    (∑ w ∈ S, p1BitToZMod (p1CanonicalLink k left v w)) =
        ∑ w ∈ S, (if H w then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      exact hbit w
    _ = ((S.filter H).card : ZMod 2) :=
      p1SumIndicator_mod2 S H
    _ = ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) := by
      rw [hfilter]
      rfl

/-- All actual raw side-facet sign indicators together have parity
equal to the prescribed omitted-base bit plus the complete
canonical link row. The sign table is genuinely evaluated on
actual erased finite vertex subsets. -/
theorem p1SidePacket_rawSign_sum
    (k : ℕ) (left : Bool) (v : Fin (4*k+6)) :
    (∑ x ∈ p1SidePacketOmitOld k v,
       p1BitToZMod
         (p1SideSignTable k left ((p1SidePacketOmitOld k v).erase x))) =
      p1BitToZMod (p1BaseVertexBit k v) +
        ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) := by
  let S : Finset (Fin (4*k+6)) :=
    (Finset.univ : Finset (Fin (4*k+6))).erase v
  let Q : Finset (Fin (4*k+6+1)) := p1SidePacketOmitOld k v
  let new : Fin (4*k+6+1) := Fin.last (4*k+6)
  let emb : Fin (4*k+6) ↪ Fin (4*k+6+1) := Fin.castSuccEmb
  let F : Fin (4*k+6+1) → ZMod 2 :=
    fun x => p1BitToZMod (p1SideSignTable k left (Q.erase x))
  have hnew : new ∈ Q := p1SidePacketOmitOld_last k v
  have hdelete : Q.erase new = S.image emb :=
    p1SidePacket_erase_last_eq_old_image k v
  have hQ : Q = insert new (S.image emb) := by
    calc
      Q = insert new (Q.erase new) :=
        (Finset.insert_erase hnew).symm
      _ = insert new (S.image emb) :=
        congrArg (fun T : Finset (Fin (4*k+6+1)) => insert new T) hdelete
  have hnot : new ∉ S.image emb :=
    p1Last_not_mem_base_image k S
  have hinj : Set.InjOn (emb : Fin (4*k+6) → Fin (4*k+6+1))
      (↑S : Set (Fin (4*k+6))) := by
    intro a _ b _ hab
    exact emb.injective hab
  have hsum :
      (∑ x ∈ Q, F x) =
        F new + ∑ w ∈ S, F (emb w) := by
    calc
      (∑ x ∈ Q, F x) =
          ∑ x ∈ insert new (S.image emb), F x := by rw [hQ]
      _ = F new + (∑ x ∈ S.image emb, F x) := by
        rw [Finset.sum_insert hnot]
      _ = F new + (∑ w ∈ S, F (emb w)) := by
        congr 1
        simpa using
          (Finset.sum_image (s := S) (g := (emb : Fin (4*k+6) → Fin (4*k+6+1)))
            (f := F) hinj)
  have hFnew : F new = p1BitToZMod (p1BaseVertexBit k v) := by
    change p1BitToZMod
      (p1SideSignTable k left ((p1SidePacketOmitOld k v).erase
        (Fin.last (4*k+6)))) = _
    rw [p1SidePacket_sign_erase_new k left v]
  have hFrow :
      (∑ w ∈ S, F (emb w)) =
      ∑ w ∈ S, p1BitToZMod (p1CanonicalLink k left v w) := by
    apply Finset.sum_congr rfl
    intro w hw
    have hne : v ≠ w := Ne.symm (Finset.mem_erase.mp hw).1
    change p1BitToZMod (p1SideSignTable k left
      ((p1SidePacketOmitOld k v).erase w.castSucc)) =
      p1BitToZMod (p1CanonicalLink k left v w)
    rw [p1SidePacket_sign_erase_old_ne k left v w hne]
  have hrowsum := p1CanonicalRow_sum_erase k left v
  calc
    (∑ x ∈ p1SidePacketOmitOld k v,
       p1BitToZMod
         (p1SideSignTable k left ((p1SidePacketOmitOld k v).erase x))) =
        F new + (∑ w ∈ S, F (emb w)) := hsum
    _ = p1BitToZMod (p1BaseVertexBit k v) +
          ((p1CanonicalRowPositiveCount k left v : ℕ) : ZMod 2) := by
      rw [hFnew, hFrow, hrowsum]

end Hypertournaments
