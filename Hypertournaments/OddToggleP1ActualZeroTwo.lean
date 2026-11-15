import Hypertournaments.OddToggleP1Naturality
import Hypertournaments.OddToggleP1ActualCoboundary

/-!
# Complete zero-or-two principle for actual constrained hypertournaments

Let n=4k+5 and A be an intrinsic n-hypertournament in the actual
toggle-zero switching class: all (n+1)-vertex packets have type 0
or odd positive minority type. For every (n+2)-vertex increasing
packet, the number of homogeneous (n+1)-facets is exactly 0 or 2.

The proof is fully geometric and uses only previously established
lemmas:
* the intrinsic at-most-two phase obstruction for actual facets;
* raw finite-set images commute with erasures;
* the type-zero indicator equals the canonical raw coboundary;
* coboundary naturality under the increasing parent embedding; and
* the field characteristic-two identity delta^2=0.

No AP obstruction or witness is asserted by this theorem. It is the
uniform zero-or-two tool needed to certify the explicit p1 bad span.
-/

namespace Hypertournaments

/-- Intrinsic zero-or-two law for the actual exceptional
n≡1 (mod4) class, without any abstract phase or cochain hypotheses
left in the theorem statement. -/
theorem Hyper.p1Toggle_actual_zero_or_two
    (k a : ℕ) (A : Hyper (4*k+5) (Fin a))
    (hA : Admissible
      (toggleZero (switchingAllowed (4*k+5))) A)
    (f : Fin (4*k+7) ↪o Fin a) :
    (Finset.univ.filter (fun i : Fin (4*k+7) =>
      localIndex A (facet f.toEmbedding i) = 0)).card = 0 ∨
    (Finset.univ.filter (fun i : Fin (4*k+7) =>
      localIndex A (facet f.toEmbedding i) = 0)).card = 2 := by
  apply A.p1Actual_zero_or_two_of_indicator f
  intro i
  let g : Fin (4*k+6) ↪o Fin a := p1OrderedFacet f i
  let e : Finset (Fin a) → ZMod 2 :=
    fun Q => p1BitToZMod (A.canonicalSignTable Q)
  let Q : Finset (Fin (4*k+7)) :=
    (Finset.univ : Finset (Fin (4*k+7))).erase i
  have hpacket :
      p1BitToZMod (decide (localIndex A g.toEmbedding = 0)) =
        coboundary e (tupleVertices g.toEmbedding) :=
    A.p1Toggle_typeZero_indicator_eq_coboundary
      k a g (hA g.toEmbedding)
  have hg :
      g.toEmbedding = facet f.toEmbedding i :=
    p1OrderedFacet_toEmbedding f i
  have hverts :
      tupleVertices g.toEmbedding = Q.image f.toEmbedding := by
    exact p1OrderedFacet_vertices f i
  calc
    (if localIndex A (facet f.toEmbedding i) = 0
      then (1 : ZMod 2) else 0) =
        p1BitToZMod (decide (localIndex A g.toEmbedding = 0)) := by
      rw [hg]
      by_cases h : localIndex A (facet f.toEmbedding i) = 0 <;>
        simp [p1BitToZMod, h]
    _ = coboundary e (tupleVertices g.toEmbedding) := hpacket
    _ = coboundary e (Q.image f.toEmbedding) := by rw [hverts]
    _ = coboundary (fun P => e (P.image f.toEmbedding)) Q :=
      (p1Coboundary_image f.toEmbedding e Q).symm

end Hypertournaments
