import Hypertournaments.OddToggleP3SwitchingParity
import Hypertournaments.Cochain

/-!
# Every finite intrinsic 3-mod-4 switching hypertournament has a potential

A finite intrinsic Hyper n in the switching family, n=4k+3,
has even raw facet parity on every genuine increasing (n+1)
packet. Thus its canonical orientation cochain is closed in
degree n. The explicit cone contraction at any chosen vertex
makes it a coboundary of a lower potential on all n-sets.

This is the CONVERSE to the potential-induced switching direction.
It is essential for treating all hypothetical amalgams rather
than only those with a preferred chosen potential.

An anchor vertex is supplied explicitly; no empty-vertex-set
or fake nonempty-type assumption is hidden.
-/

namespace Hypertournaments

/-- Every intrinsic finite p3 switching hypertournament on a
nonempty finite vertex set has its genuine canonical orientation
table represented by the unsigned coboundary of one F₂ cochain. -/
theorem Hyper.p3Switching_has_canonical_potential
    (k a : ℕ) (root : Fin a)
    (E : Hyper (4*k+3) (Fin a))
    (hE : Admissible (switchingAllowed (4*k+3)) E) :
    ∃ z : Finset (Fin a) → ZMod 2,
      ∀ Q : Finset (Fin a), Q.card = 4*k+3 →
        p1BitToZMod (E.canonicalSignTable Q) =
          coboundary z Q := by
  let e : Finset (Fin a) → ZMod 2 :=
    fun Q => p1BitToZMod (E.canonicalSignTable Q)
  have hclosed (Q : Finset (Fin a))
      (hQ : Q.card = (4*k+3)+1) :
      coboundary e Q = 0 := by
    have hcard : Q.card = 4*k+4 := by omega
    let f : Fin (4*k+4) ↪o Fin a := Q.orderEmbOfFin hcard
    have hloc : localIndex E f.toEmbedding ∈
        switchingAllowed (4*k+3) := hE f.toEmbedding
    have hh :=
      (E.p3SwitchingAllowed_iff_coboundary_zero k a f).mp hloc
    have hvertices : tupleVertices f.toEmbedding = Q := by
      dsimp [f, tupleVertices]
      exact Finset.image_orderEmbOfFin_univ Q hcard
    change coboundary e (tupleVertices f.toEmbedding) = 0 at hh
    rwa [hvertices] at hh
  refine ⟨contractAt root e, ?_⟩
  intro Q hQ
  exact (cocycle_exact_at_card root (4*k+3) e hclosed Q hQ).symm

end Hypertournaments
