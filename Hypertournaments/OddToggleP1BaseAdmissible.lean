import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1BaseParity
import Hypertournaments.OddToggleP1MissingSets
import Hypertournaments.OddToggleP1EvenRawAllowed
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# Unconditional admissibility of the actual explicit p1 common base

The one-point nonamalgamation diagram for n=4k+5 has an old common
base of size exactly n+1=4k+6. It therefore has a unique full
increasing local packet. Its raw facet signs agree with the
prescribed base vertex bits, which have exact positive count
4k+4, hence even parity.

The previously kernel-certified even-raw-parity criterion implies
its intrinsic local type belongs to the exceptional allowed family.
Permutation invariance then certifies Admissible for *all*
injective tuples, not merely for the displayed canonical order.
-/

namespace Hypertournaments

/-- Every increasing full-length enumeration of Fin(4k+6)
has the entire vertex set as its range. -/
theorem p1Base_fullVertices (k : ℕ)
    (f : Fin (4*k+6) ↪o Fin (4*k+6)) :
    tupleVertices f.toEmbedding = Finset.univ := by
  have hsize : (tupleVertices f.toEmbedding).card = 4*k+6 := by
    dsimp [tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [hsize]

/-- The full increasing self-embedding on Fin(4k+6) is
coordinatewise the identity. -/
theorem p1Base_fullOrderedTuple_id (k : ℕ)
    (f : Fin (4*k+6) ↪o Fin (4*k+6))
    (i : Fin (4*k+6)) : f i = i := by
  have hfull := p1Base_fullVertices k f
  have hleft := card_lt_tupleVertices_eq f i
  rw [hfull] at hleft
  have hright :
      ((Finset.univ : Finset (Fin (4*k+6))).filter (· < f i)).card =
        (f i).val := by
    change (Finset.univ.filter (fun j : Fin (4*k+6) =>
      j.val < (f i).val)).card = (f i).val
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right (Nat.le_of_lt (f i).isLt)
  apply Fin.ext
  omega

/-- Every facet sign of the single full ordered base packet
is exactly the literal prescribed sign of the omitted vertex. -/
theorem p1BaseHyper_full_rawSigns (k : ℕ)
    (f : Fin (4*k+6) ↪o Fin (4*k+6))
    (i : Fin (4*k+6)) :
    (p1BaseHyper k).orient (facet f.toEmbedding i) =
      p1BaseVertexBit k i := by
  have hfull := p1Base_fullVertices k f
  have hi := p1Base_fullOrderedTuple_id k f i
  calc
    (p1BaseHyper k).orient (facet f.toEmbedding i) =
        p1BaseSignTable k (tupleVertices (facet f.toEmbedding i)) :=
      fromOrderedSigns_facet_increasing (p1BaseSignTable k) f i
    _ = p1BaseSignTable k
          ((Finset.univ : Finset (Fin (4*k+6))).erase i) := by
      have he : f.toEmbedding i = i := hi
      rw [tupleVertices_facet_eq_erase f.toEmbedding i, hfull, he]
    _ = p1BaseVertexBit k i := p1BaseSignTable_erase k i

/-- The sole increasing local packet in the actual common base is
an allowed odd-minority type, because its raw sign count is even. -/
theorem p1BaseHyper_increasing_allowed (k : ℕ)
    (f : Fin (4*k+6) ↪o Fin (4*k+6)) :
    localIndex (p1BaseHyper k) f.toEmbedding ∈
      toggleZero (switchingAllowed (4*k+5)) := by
  have hbits :
      (fun i : Fin (4*k+6) =>
        (p1BaseHyper k).orient (facet f.toEmbedding i)) =
      (fun i : Fin (4*k+6) => p1BaseVertexBit k i) := by
    funext i
    exact p1BaseHyper_full_rawSigns k f i
  have heven :
      boolPacketPositiveCount
        (fun i : Fin (4*k+6) =>
          (p1BaseHyper k).orient (facet f.toEmbedding i)) % 2 = 0 := by
    rw [hbits]
    exact p1BaseVertexBit_even k
  exact (p1BaseHyper k).p1Toggle_allowed_of_even_rawFacetCount
    k f.toEmbedding heven

/-- **Actual** intrinsic p1 base age membership, unconditional
and uniform for all k≥0. -/
theorem p1BaseHyper_admissible (k : ℕ) :
    Admissible (toggleZero (switchingAllowed (4*k+5)))
      (p1BaseHyper k) := by
  apply (admissible_iff_canonical_all
    (toggleZero (switchingAllowed (4*k+5)))
    (p1BaseHyper k)).2
  intro Q hQ
  exact p1BaseHyper_increasing_allowed k (Q.orderEmbOfFin hQ)

end Hypertournaments
