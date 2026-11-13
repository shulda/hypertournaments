import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3CanonicalFreshQAll
import Hypertournaments.OddToggleP3ActualProtectedSidePackets
import Hypertournaments.OddToggleP3CanonicalSides

/-!
# Full-block q=m genuine canonical p3 one-fresh side packet age

We now have exact actual one-fresh packet geometry: whenever every
old block is occupied, any chosen triple of consecutive old block
labels provides two old singleton vertices on opposite deletion
parities. If this triple belongs to a protectedBlocks block family
disjoint from the eligible missing-half support of the side's
new-point potential, deleting either singleton kills its entire
protectedBlocks block and forces a genuine raw-zero orientation facet.

The already certified actual protectedBlocks-packet criterion therefore
places every such packet in toggleZero(switchingAllowed), for ALL
base and link coefficient assignments W,L. The protectedBlocks triple
and disjointness hypotheses are explicit; the canonical left/right
half choices are separate final instantiations.

This is genuine intrinsic Hyper age, not a synthetic sign system,
and does not assert ordinary non-amalgamation.
-/

namespace Hypertournaments

/-- Every actual canonical one-fresh packet meeting ALL m old blocks
is admitted in the exceptional p3 age if some protectedBlocks consecutive
triple lies outside the eligible new-link support. -/
theorem p3CanonicalSide_allowed_qAll_fresh_packet
    (k m t : ℕ) (hk : 1 ≤ k) (hm : m = 4*k+2) (ht : 0 < t)
    (eligible protectedBlocks : Finset (Fin m))
    (hDisjoint : Disjoint eligible protectedBlocks)
    (start : ℕ) (hstart : start+2 < m)
    (hProtected : ∀ b : Fin m,
      start ≤ b.val → b.val ≤ start+2 → b ∈ protectedBlocks)
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hFresh : Fin.last (m*t) ∈ tupleVertices f.toEmbedding)
    (hAll : ∀ i : Fin m,
      ∃ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding ∧
        p3BlockNumber t z = i.val) :
    localIndex (p3CanonicalSide m t eligible W L) f.toEmbedding ∈
      toggleZero (switchingAllowed (m+1)) := by
  obtain ⟨x,y,v,w,hmod,hRangeV,hRangeW,hV,hW,hUniqueV,hUniqueW⟩ :=
    p3CanonicalFresh_qAll_protected_singleton_positions
      m t ht f hFresh hAll start hstart
  let i : Fin m := p3BlockLabel m t ht v
  let j : Fin m := p3BlockLabel m t ht w
  have hi : i ∈ protectedBlocks := by
    apply hProtected i
    · exact hRangeV.1
    · exact hRangeV.2
  have hj : j ∈ protectedBlocks := by
    apply hProtected j
    · exact hRangeW.1
    · exact hRangeW.2
  have hVI : p3BlockNumber t v = i.val := rfl
  have hWJ : p3BlockNumber t w = j.val := rfl
  have hUniqueVI : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = i.val → z=v := by
    intro z hz hBlock
    exact hUniqueV z hz hBlock
  have hUniqueWJ : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = j.val → z=w := by
    intro z hz hBlock
    exact hUniqueW z hz hBlock
  have hParity :
      decide (x.castSucc.val%2=1) ≠ decide (y.castSucc.val%2=1) := by
    change decide (x.val%2=1) ≠ decide (y.val%2=1)
    by_cases hx : x.val%2=1
    · have hy : y.val%2≠1 := by omega
      simp [hx, hy]
    · have hy : y.val%2=1 := by omega
      simp [hx, hy]
  subst m
  have hN : (4*k+2)+1 = 4*k+3 := by omega
  have hP : ((4*k+2)+1)+1 = 4*k+4 := by omega
  simp only [hN, hP] at *
  change localIndex
    (p3SideHyper (4*k+2) t
      (Fin.castSuccOrderEmb : Fin ((4*k+2)*t) ↪o
        Fin ((4*k+2)*t+1)).toEmbedding
      (Fin.last ((4*k+2)*t)) eligible W L)
    f.toEmbedding ∈ toggleZero (switchingAllowed (4*k+3))
  exact p3SidePacket_allowed_of_two_protected_singletons
    k t ((4*k+2)*t+1)
    (Fin.castSuccOrderEmb : Fin ((4*k+2)*t) ↪o
      Fin ((4*k+2)*t+1)).toEmbedding
    (Fin.last ((4*k+2)*t))
    eligible protectedBlocks hDisjoint W L f
    x.castSucc y.castSucc hParity
    i j hi hj v w hV hW hVI hWJ hUniqueVI hUniqueWJ

end Hypertournaments
