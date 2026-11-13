import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3CanonicalFreshQMinusOne
import Hypertournaments.OddToggleP3MissingSingletonPacket
import Hypertournaments.OddToggleP3CanonicalSides

/-!
# Genuine canonical p3 one-fresh side: q=m−1 occupied block case

The complete q=m−1 geometry is now certified on ACTUAL packets:
a fresh-containing packet has its fresh point last and its old
prefix contains singleton vertices of opposite deletion parity.
If one block is absent, deleting either singleton removes a second
block and forces a true zero orientation facet.

This theorem combines that real-packet geometry with the already
certified true Hyper support/coboundary and switching arguments.
It makes no assumptions on W or L coefficients and excludes the
homogeneous type for every such packet.

The q≤m−2 and q=m branches, full side admissibility, and the
ordinary non-AP obstruction remain separate obligations.
-/

namespace Hypertournaments

/-- Every genuine canonical side packet with one fresh vertex,
all old blocks except one occupied, and that block absent, is
in the required exceptional p3 age, uniformly in W and L. -/
theorem p3CanonicalSide_allowed_qMinusOne_fresh_packet
    (k m t : ℕ) (hk : 1 ≤ k) (hm : m = 4*k+2) (ht : 0 < t)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hFresh : Fin.last (m*t) ∈ tupleVertices f.toEmbedding)
    (missing : Fin m)
    (hMissing : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t z ≠ missing.val)
    (hOthers : ∀ i : Fin m, i ≠ missing →
      ∃ z : Fin (m*t),
        z.castSucc ∈ tupleVertices f.toEmbedding ∧
        p3BlockNumber t z = i.val) :
    localIndex (p3CanonicalSide m t eligible W L) f.toEmbedding ∈
      toggleZero (switchingAllowed (m+1)) := by
  have hm6 : 6 ≤ m := by omega
  obtain ⟨x,y,v,w,hEven,hOdd,hV,hW,hUniqueV,hUniqueW⟩ :=
    p3CanonicalFresh_qMinusOne_singleton_positions
      m t hm6 f hFresh missing hOthers
  have hVmem : v.castSucc ∈ tupleVertices f.toEmbedding :=
    Finset.mem_image.mpr
      ⟨x.castSucc, Finset.mem_univ _, hV.symm⟩
  have hWmem : w.castSucc ∈ tupleVertices f.toEmbedding :=
    Finset.mem_image.mpr
      ⟨y.castSucc, Finset.mem_univ _, hW.symm⟩
  let i : Fin m := p3BlockLabel m t ht v
  let j : Fin m := p3BlockLabel m t ht w
  have hMissingI : missing ≠ i := by
    intro heq
    apply hMissing v hVmem
    have heq' := congrArg Fin.val heq.symm
    exact heq'
  have hMissingJ : missing ≠ j := by
    intro heq
    apply hMissing w hWmem
    exact congrArg Fin.val heq.symm
  have hUniqueVI : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = i.val → z=v := by
    intro z hz hlabel
    exact hUniqueV z hz hlabel
  have hUniqueWJ : ∀ z : Fin (m*t),
      z.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t z = j.val → z=w := by
    intro z hz hlabel
    exact hUniqueW z hz hlabel
  have hParity :
      decide (x.castSucc.val%2=1) ≠ decide (y.castSucc.val%2=1) := by
    change decide (x.val%2=1) ≠ decide (y.val%2=1)
    simp [hEven, hOdd]
  subst m
  have hN : (4*k+2)+1=4*k+3 := by omega
  have hP : ((4*k+2)+1)+1=4*k+4 := by omega
  simp only [hN, hP] at *
  change localIndex
    (p3SideHyper (4*k+2) t
      (Fin.castSuccOrderEmb : Fin ((4*k+2)*t) ↪o
        Fin ((4*k+2)*t+1)).toEmbedding
      (Fin.last ((4*k+2)*t)) eligible W L)
    f.toEmbedding ∈
      toggleZero (switchingAllowed (4*k+3))
  exact p3SidePacket_allowed_of_missing_and_two_singletons
    k t ((4*k+2)*t+1)
    (Fin.castSuccOrderEmb : Fin ((4*k+2)*t) ↪o
      Fin ((4*k+2)*t+1)).toEmbedding
    (Fin.last ((4*k+2)*t))
    eligible W L f missing hMissing
    x.castSucc y.castSucc hParity
    i j hMissingI hMissingJ
    v w hV hW hUniqueVI hUniqueWJ

end Hypertournaments
