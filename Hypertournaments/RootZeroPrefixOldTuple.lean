import Mathlib.Order.Fin.Tuple
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.CanonicalPacket

/-!
# Prefixing a least distinguished root to an increasing old tuple

For the rooted odd suspension, the canonical old root has index zero.
If an increasing old n-tuple avoids this root, the root is strictly
smaller than all of its entries. Prefixing it produces the unique
increasing (n+1)-tuple whose range is exactly the root together with
the original range.

This elementary fact is the exact ordered-packet geometry needed to
apply the root-absent three-pad +1 minority-count lemma to a genuine
source hypertournament packet.
-/

namespace Hypertournaments

/-- A least root absent from an increasing tuple can be prepended
canonically, with exact positional and finite-set identities. -/
theorem exists_increasing_tuple_prefix_zero_root
    {n a : ℕ} (root : Fin a) (hroot0 : root.val = 0)
    (t : Fin n ↪o Fin a)
    (hnot : root ∉ tupleVertices t.toEmbedding) :
    ∃ g : Fin (n+1) ↪o Fin a,
      g (0 : Fin (n+1)) = root ∧
      (∀ j : Fin n, g j.succ = t j) ∧
      tupleVertices g.toEmbedding =
        insert root (tupleVertices t.toEmbedding) := by
  have hrootlt (j : Fin n) : root < t j := by
    have hneq : t j ≠ root := by
      intro he
      apply hnot
      have hj : t j ∈ tupleVertices t.toEmbedding :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      simpa [he] using hj
    change root.val < (t j).val
    have hpos : (t j).val ≠ 0 := by
      intro hh
      apply hneq
      apply Fin.ext
      omega
    omega
  let gFun : Fin (n+1) → Fin a :=
    Fin.cons root (fun j : Fin n => t j)
  have hstrict : StrictMono gFun :=
    (Fin.strictMono_cons).2 ⟨hrootlt, t.strictMono⟩
  let g : Fin (n+1) ↪o Fin a :=
    OrderEmbedding.ofStrictMono gFun hstrict
  refine ⟨g, ?_, ?_, ?_⟩
  · rfl
  · intro j
    rfl
  · ext v
    simp only [tupleVertices, Finset.mem_insert,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        left
        have hh : root = v := by
          simpa [g, gFun, Fin.cons] using hi
        exact hh.symm
      · intro hi
        right
        refine ⟨j, ?_⟩
        simpa [g, gFun, Fin.cons] using hi
    · rintro (he | ⟨j, hj⟩)
      · refine ⟨0, ?_⟩
        simpa [g, gFun, Fin.cons] using he.symm
      · refine ⟨j.succ, ?_⟩
        simpa [g, gFun, Fin.cons] using hj

end Hypertournaments
