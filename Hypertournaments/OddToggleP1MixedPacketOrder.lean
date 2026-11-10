import Hypertournaments.OddToggleP1MixedJointGeometry
import Hypertournaments.CanonicalPacket

/-!
# Increasing mixed packets place the new endpoints at the final positions

A mixed local packet on a canonical two-point joint is obtained by
omitting two *old* vertices. Its greatest two vertices are therefore
the left new vertex and the right new vertex, in that order. We
identify their exact locations in the increasing local tuple.
This is necessary for converting homogeneous raw facet alternation
into the link-table disagreement obstruction.
-/

namespace Hypertournaments

theorem p1JointMixedPacket_sorted_endpoints (k : ℕ)
    (v w : Fin (4*k+6)) (hvw : v ≠ w)
    (hQ : (p1JointMixedPacket k v w).card = 4*k+6) :
    let g := (p1JointMixedPacket k v w).orderEmbOfFin hQ
    g (⟨4*k+4, by omega⟩ : Fin (4*k+6)) = p1JointLeftNew k ∧
    g (Fin.last (4*k+5)) = p1JointRightNew k := by
  let Q : Finset (Fin (4*k+6+2)) := p1JointMixedPacket k v w
  let g : Fin (4*k+6) ↪o Fin (4*k+6+2) := Q.orderEmbOfFin hQ
  have hRange : Finset.univ.image g = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  have hRmem : p1JointRightNew k ∈ Finset.univ.image g := by
    rw [hRange]
    exact (p1JointMixedPacket_new_mem k v w).2
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hRmem
  have hright : g (Fin.last (4*k+5)) = p1JointRightNew k := by
    have hlastIdx : j = Fin.last (4*k+5) := by
      by_contra hne
      have hlt : j < Fin.last (4*k+5) := by
        change j.val < 4*k+5
        have hb := j.isLt
        have hnot : j.val ≠ 4*k+5 := by
          intro he
          apply hne
          apply Fin.ext
          simpa only [Fin.val_last] using he
        omega
      have hbad : p1JointRightNew k < p1JointRightNew k := by
        calc
          p1JointRightNew k = g j := hj.symm
          _ < g (Fin.last (4*k+5)) := g.strictMono hlt
          _ ≤ p1JointRightNew k := Fin.le_last _
      exact (lt_irrefl _) hbad
    simpa only [hlastIdx] using hj
  have hLmem : p1JointLeftNew k ∈ Finset.univ.image g := by
    rw [hRange]
    exact (p1JointMixedPacket_new_mem k v w).1
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hLmem
  have hiNotLast : i ≠ Fin.last (4*k+5) := by
    intro he
    have hbad : p1JointLeftNew k = p1JointRightNew k := by
      calc
        p1JointLeftNew k = g i := hi.symm
        _ = g (Fin.last (4*k+5)) := by rw [he]
        _ = p1JointRightNew k := hright
    exact (ne_of_lt (p1JointLeft_lt_right k)) hbad
  let q : Fin (4*k+6) := ⟨4*k+4, by omega⟩
  have hle : i ≤ q := by
    change i.val ≤ 4*k+4
    have hb := i.isLt
    have hnot : i.val ≠ 4*k+5 := by
      intro he
      apply hiNotLast
      apply Fin.ext
      simpa only [Fin.val_last] using he
    omega
  have hLle : p1JointLeftNew k ≤ g q := by
    calc
      p1JointLeftNew k = g i := hi.symm
      _ ≤ g q := g.monotone hle
  have hqLast : q < Fin.last (4*k+5) := by
    change 4*k+4 < 4*k+5
    omega
  have hqRight : g q < p1JointRightNew k := by
    calc
      g q < g (Fin.last (4*k+5)) := g.strictMono hqLast
      _ = p1JointRightNew k := hright
  have hleft : g q = p1JointLeftNew k := by
    apply Fin.ext
    have hlo : (p1JointLeftNew k).val ≤ (g q).val := hLle
    have hhi : (g q).val < (p1JointRightNew k).val := hqRight
    dsimp [p1JointLeftNew, p1JointRightNew] at hlo hhi
    omega
  exact ⟨hleft, hright⟩

end Hypertournaments
