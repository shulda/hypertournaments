import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1MixedPacketOrder
import Hypertournaments.OddToggleP1Core
import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# The final old facet positions in two critical p1 mixed packets

For any genuine mixed joint packet, if z is its largest remaining
old vertex, its increasing enumeration puts z immediately before
the two newly introduced endpoints. Apply this to the two decisive
mixed packets omitting old core pairs (a2,a4) and (a2,a5): their
final old deletions are respectively a5 and a4, both at index
4k+3. This synchronizes the raw facet phases in the eventual
forced-facet contradiction.
-/

namespace Hypertournaments

/-- The greatest old vertex of a genuine mixed packet appears at
the third-from-last position of its increasing enumeration. -/
theorem p1JointMixedPacket_thirdLast_of_max_old
    (k : ℕ) (v w : Fin (4*k+6)) (hvw : v ≠ w)
    (hQ : (p1JointMixedPacket k v w).card = 4*k+6)
    (z : Fin (4*k+6+2))
    (hzmem : z ∈ p1JointMixedPacket k v w)
    (hzold : z < p1JointLeftNew k)
    (hzmax : ∀ t ∈ p1JointMixedPacket k v w,
       t < p1JointLeftNew k → t ≤ z) :
    (p1JointMixedPacket k v w).orderEmbOfFin hQ
      (⟨4*k+3, by omega⟩ : Fin (4*k+6)) = z := by
  let Q : Finset (Fin (4*k+6+2)) := p1JointMixedPacket k v w
  let g : Fin (4*k+6) ↪o Fin (4*k+6+2) := Q.orderEmbOfFin hQ
  let q : Fin (4*k+6) := ⟨4*k+3, by omega⟩
  let i0 : Fin (4*k+6) := ⟨4*k+4, by omega⟩
  have hsort := p1JointMixedPacket_sorted_endpoints k v w hvw hQ
  have hleft : g i0 = p1JointLeftNew k := hsort.1
  have hrange : (Finset.univ : Finset (Fin (4*k+6))).image g = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  have hzImage : z ∈ (Finset.univ : Finset (Fin (4*k+6))).image g := by
    rw [hrange]
    exact hzmem
  obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hzImage
  have hiless : i < i0 := by
    by_contra hnot
    have hge : i0 ≤ i := le_of_not_gt hnot
    have hbad : p1JointLeftNew k ≤ z := by
      calc
        p1JointLeftNew k = g i0 := hleft.symm
        _ ≤ g i := g.monotone hge
        _ = z := hiz
    exact (not_le_of_gt hzold) hbad
  have hle : i ≤ q := by
    change i.val ≤ 4*k+3
    have hnum : i.val < 4*k+4 := hiless
    omega
  have hge : z ≤ g q := by
    calc
      z = g i := hiz.symm
      _ ≤ g q := g.monotone hle
  have hqless : q < i0 := by
    change 4*k+3 < 4*k+4
    omega
  have hqold : g q < p1JointLeftNew k := by
    calc
      g q < g i0 := g.strictMono hqless
      _ = p1JointLeftNew k := hleft
  have hqmem : g q ∈ Q := by
    rw [← hrange]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  have hleq : g q ≤ z := hzmax (g q) hqmem hqold
  exact le_antisymm hleq hge

/-- For the homogeneous candidate Q(a2,a4), the last old facet
deletion is a5 at index 4k+3. -/
theorem p1JointMixed24_thirdLast_a5 (k : ℕ)
    (hQ : (p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6))).card = 4*k+6) :
    (p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6))).orderEmbOfFin hQ
        (⟨4*k+3, by omega⟩ : Fin (4*k+6)) =
      p1JointOld k (p1CoreAt k (5 : Fin 6)) := by
  let a2 := p1JointOld k (p1CoreAt k (2 : Fin 6))
  let a4 := p1JointOld k (p1CoreAt k (4 : Fin 6))
  let a5 := p1JointOld k (p1CoreAt k (5 : Fin 6))
  have h24 : a2 < a4 := by
    change 4*k+2 < 4*k+4
    omega
  have h45 : a4 < a5 := by
    change 4*k+4 < 4*k+5
    omega
  have hmem : a5 ∈ p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6)) := by
    apply Finset.mem_erase.mpr
    exact ⟨ne_of_gt h45,
      Finset.mem_erase.mpr ⟨ne_of_gt (lt_trans h24 h45), Finset.mem_univ _⟩⟩
  have hlt : a5 < p1JointLeftNew k := by
    change 4*k+5 < 4*k+6
    omega
  have hmax : ∀ t ∈ p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6)),
      t < p1JointLeftNew k → t ≤ a5 := by
    intro t _ ht
    change t.val ≤ 4*k+5
    have hb : t.val < 4*k+6 := ht
    omega
  have hne : p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (4 : Fin 6) := by
    intro hh
    have he := congrArg Fin.val hh
    change 4*k+2 = 4*k+4 at he
    omega
  exact p1JointMixedPacket_thirdLast_of_max_old k _ _ hne hQ
    a5 hmem hlt hmax

/-- For Q(a2,a5), the last old facet deletion is a4
at exactly the same index 4k+3. -/
theorem p1JointMixed25_thirdLast_a4 (k : ℕ)
    (hQ : (p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6))).card = 4*k+6) :
    (p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6))).orderEmbOfFin hQ
        (⟨4*k+3, by omega⟩ : Fin (4*k+6)) =
      p1JointOld k (p1CoreAt k (4 : Fin 6)) := by
  let a2 := p1JointOld k (p1CoreAt k (2 : Fin 6))
  let a4 := p1JointOld k (p1CoreAt k (4 : Fin 6))
  let a5 := p1JointOld k (p1CoreAt k (5 : Fin 6))
  have h24 : a2 < a4 := by
    change 4*k+2 < 4*k+4
    omega
  have h45 : a4 < a5 := by
    change 4*k+4 < 4*k+5
    omega
  have hmem : a4 ∈ p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6)) := by
    apply Finset.mem_erase.mpr
    exact ⟨ne_of_lt h45,
      Finset.mem_erase.mpr ⟨ne_of_gt h24, Finset.mem_univ _⟩⟩
  have hlt : a4 < p1JointLeftNew k := by
    change 4*k+4 < 4*k+6
    omega
  have hmax : ∀ t ∈ p1JointMixedPacket k
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6)),
      t < p1JointLeftNew k → t ≤ a4 := by
    intro t ht htl
    have hnot : t ≠ a5 := (Finset.mem_erase.mp ht).1
    have hbound : t.val < 4*k+6 := htl
    have hnot5 : t.val ≠ 4*k+5 := by
      intro he
      apply hnot
      apply Fin.ext
      exact he
    change t.val ≤ 4*k+4
    omega
  have hne : p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (5 : Fin 6) := by
    intro hh
    have he := congrArg Fin.val hh
    change 4*k+2 = 4*k+5 at he
    omega
  exact p1JointMixedPacket_thirdLast_of_max_old k _ _ hne hQ
    a4 hmem hlt hmax

end Hypertournaments
