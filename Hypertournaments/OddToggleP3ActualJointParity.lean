import Hypertournaments.OddToggleP3DoubleConeParity
import Hypertournaments.OddToggleP3SwitchingParity
import Hypertournaments.OddToggleP3BasePreservation

/-!
# Genuine p3 switching joints satisfy the mixed parity equation

Let E be any actual intrinsic arity n=4k+3 hyperturnament with
all (n+1)-packets in switchingAllowed. Embed the old base by
an arbitrary injection old, with two distinct fresh vertices l,r.
For every old (n-1)-subset Q, the parent packet Q∪{l,r} has zero
raw canonical orientation coboundary by intrinsic switching
admissibility. The exact two-cone packet identity implies that
the pulled-back mixed orientation cochain
   x(U) = contractAt r (contractAt l e) (old[U])
satisfies on every Q
   δx(Q) = e(old[Q]∪{l}) + e(old[Q]∪{r}).

Crucially this applies to EVERY actual hypothetical switching
joint E, regardless of how it arose or whether it has a preferred
potential representation; no additional order belongs to the
hypertournament language. Side admissibility and the identification
case of ordinary AP are separate.
-/

namespace Hypertournaments

/-- Every actual finite switching joint satisfies the exact
mixed-facet parity equation on all old m-subsets, without any
chosen joint potential. -/
theorem Hyper.p3ActualJoint_mixedParity
    (k a : ℕ)
    (E : Hyper (4*k+3) (Fin (a+2)))
    (hE : Admissible (switchingAllowed (4*k+3)) E)
    (old : Fin a ↪ Fin (a+2))
    (l r : Fin (a+2)) (hlr : l ≠ r)
    (hFresh : ∀ v : Fin a, old v ≠ l ∧ old v ≠ r)
    (Q : Finset (Fin a)) (hQ : Q.card = 4*k+2) :
    coboundary
      (fun U : Finset (Fin a) =>
        contractAt r
          (contractAt l
            (fun T : Finset (Fin (a+2)) =>
              p1BitToZMod (E.canonicalSignTable T)))
          (U.image old)) Q =
      p1BitToZMod (E.canonicalSignTable (insert l (Q.image old))) +
      p1BitToZMod (E.canonicalSignTable (insert r (Q.image old))) := by
  classical
  let e : Finset (Fin (a+2)) → ZMod 2 :=
    fun T => p1BitToZMod (E.canonicalSignTable T)
  let S : Finset (Fin (a+2)) := Q.image old
  have hcardS : S.card = 4*k+2 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ old.injective]
    exact hQ
  have hls : l ∉ S := by
    intro h
    obtain ⟨v, _, heq⟩ := Finset.mem_image.mp h
    exact (hFresh v).1 heq
  have hrs : r ∉ S := by
    intro h
    obtain ⟨v, _, heq⟩ := Finset.mem_image.mp h
    exact (hFresh v).2 heq
  have hlRS : l ∉ insert r S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hlr, hls⟩
  have hcardR : (insert r S).card = S.card + 1 := by
    simp [hrs]
  have hcardP : (insert l (insert r S)).card = 4*k+4 := by
    have hcardL : (insert l (insert r S)).card = (insert r S).card + 1 := by
      simp [hlRS]
    omega
  let P : Finset (Fin (a+2)) := insert l (insert r S)
  let f : Fin (4*k+4) ↪o Fin (a+2) :=
    P.orderEmbOfFin hcardP
  have htype : localIndex E f.toEmbedding ∈ switchingAllowed (4*k+3) :=
    hE f.toEmbedding
  have hz := (E.p3SwitchingAllowed_iff_coboundary_zero k (a+2) f).mp htype
  have hvertices : tupleVertices f.toEmbedding = P := by
    dsimp [tupleVertices, f]
    exact Finset.image_orderEmbOfFin_univ P hcardP
  change coboundary e (tupleVertices f.toEmbedding) = 0 at hz
  rw [hvertices] at hz
  have hparent : coboundary e (insert l (insert r S)) = 0 := hz
  have hraw := p3DoubleCone_mixed_parity_of_zero
    l r hlr e S hls hrs hparent
  let x : Finset (Fin a) → ZMod 2 :=
    fun U => contractAt r (contractAt l e) (U.image old)
  have hrestriction : coboundary (contractAt r (contractAt l e)) S =
      coboundary x Q :=
    p3Coboundary_image_injective old x
      (contractAt r (contractAt l e))
      (by intro U; rfl) Q
  change coboundary x Q =
    e (insert l S) + e (insert r S)
  exact hrestriction.symm.trans hraw

end Hypertournaments
