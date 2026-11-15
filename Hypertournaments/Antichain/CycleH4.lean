import Hypertournaments.Antichain.CycleQ
import Hypertournaments.Antichain.SumInduced
import Hypertournaments.Antichain.HomogeneousPacket
import Hypertournaments.GeneralLocalIndexInvariant
import Hypertournaments.OddToggleP1Homogeneous
import Mathlib.Data.Fintype.Perm

/-!
# Four-vertex copies in the cycle construction

The intrinsic homogeneous four-vertex type has local index zero. In a
sum-induced cycle tournament its vertex sets are exactly the induced copies
of a three-vertex path and an isolated vertex in the underlying cycle.
-/

namespace Hypertournaments.Antichain

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def fourGraph (a b c d : Bool) (i j : Fin 4) : Bool :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then a else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then b else
  if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then c else
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then d else false

private def fourQFrame (g : Fin 4 → Fin 4 → Bool) (σ : Equiv.Perm (Fin 4)) : Prop :=
  g (σ 0) (σ 1) = true ∧ g (σ 1) (σ 2) = true ∧
    g (σ 0) (σ 2) = false ∧ g (σ 0) (σ 3) = false ∧
    g (σ 1) (σ 3) = false ∧ g (σ 2) (σ 3) = false

private theorem fourQFrame_iff (a b c d : Bool) :
    (∃ σ : Equiv.Perm (Fin 4), fourQFrame (fourGraph a b c d) σ) ↔
      a ≠ c ∧ b ≠ d := by
  have h : ∀ a b c d : Bool,
      (∃ σ : Equiv.Perm (Fin 4), fourQFrame (fourGraph a b c d) σ) ↔
        a ≠ c ∧ b ≠ d := by
    unfold fourQFrame fourGraph
    decide +kernel
  exact h a b c d

private def fourRaw (a b c d : Bool) (i : Fin 4) : Bool :=
  if i = 0 then b ^^ c else if i = 1 then c ^^ d else
    if i = 2 then a ^^ d else a ^^ b

private theorem fourRaw_constant_iff (a b c d : Bool) :
    (∃ z : Bool, ∀ i : Fin 4, (fourRaw a b c d i ^^ decide (i.val % 2 = 1)) = z) ↔
      a ≠ c ∧ b ≠ d := by
  have h : ∀ a b c d : Bool,
      (∃ z : Bool, ∀ i : Fin 4, (fourRaw a b c d i ^^ decide (i.val % 2 = 1)) = z) ↔
        a ≠ c ∧ b ≠ d := by decide +kernel
  exact h a b c d

private theorem cycle_diagonals {N : ℕ} (f : Fin 4 ↪o Fin N) :
    ¬ cycleAdj (f 0) (f 2) ∧ ¬ cycleAdj (f 1) (f 3) := by
  have h01 := f.strictMono (show (0 : Fin 4) < 1 by decide)
  have h12 := f.strictMono (show (1 : Fin 4) < 2 by decide)
  have h23 := f.strictMono (show (2 : Fin 4) < 3 by decide)
  simp only [cycleAdj, Fin.lt_def] at *
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  have h2 := (f 2).isLt
  have h3 := (f 3).isLt
  omega

private theorem cycle_sorted_graph {N : ℕ} (hN : 2 ≤ N) (f : Fin 4 ↪o Fin N)
    (i j : Fin 4) :
    decide (cycleAdj (f i) (f j)) =
      fourGraph (decide (cycleAdj (f 0) (f 1))) (decide (cycleAdj (f 1) (f 2)))
        (decide (cycleAdj (f 2) (f 3))) (decide (cycleAdj (f 0) (f 3))) i j := by
  have hd := cycle_diagonals f
  have hs (x y : Fin N) : decide (cycleAdj x y) = decide (cycleAdj y x) := by
    simp only [cycleAdj_symm x y]
  fin_cases i <;> fin_cases j <;>
    simp [fourGraph, cycleAdj_irrefl hN, hd.1, hd.2, hs (f 1) (f 0),
      hs (f 2) (f 0), hs (f 2) (f 1), hs (f 3) (f 0),
      hs (f 3) (f 1), hs (f 3) (f 2)]

private theorem tournamentBit_cycle_forward {N : ℕ} {a b : Fin N} (hab : a < b) :
    tournamentBit (cycleTournament N) a b = bit (decide (cycleAdj a b)) := by
  rw [tournamentBit_of_ne _ (ne_of_lt hab)]
  simp [cycleTournament, cycleTournamentBit, Function.Embedding.embFinTwo_apply_zero,
    Function.Embedding.embFinTwo_apply_one, not_lt.mpr (le_of_lt hab)]
  rfl

private theorem cycle_sorted_facet {N : ℕ} (f : Fin 4 ↪o Fin N) (i : Fin 4) :
    (sumInduced (cycleTournament N) 3).orient (facet f.toEmbedding i) =
      fourRaw (decide (cycleAdj (f 0) (f 1))) (decide (cycleAdj (f 1) (f 2)))
        (decide (cycleAdj (f 2) (f 3))) (decide (cycleAdj (f 0) (f 3))) i := by
  apply bit_injective
  rw [sumInduced_orient, pairSum_three]
  have hmono : StrictMono (facet f.toEmbedding i : Fin 3 → Fin N) :=
    f.strictMono.comp (Fin.strictMono_succAbove i)
  rw [tournamentBit_cycle_forward (hmono (show (0 : Fin 3) < 1 by decide)),
    tournamentBit_cycle_forward (hmono (show (0 : Fin 3) < 2 by decide)),
    tournamentBit_cycle_forward (hmono (show (1 : Fin 3) < 2 by decide))]
  have hd := cycle_diagonals f
  fin_cases i <;>
    simp [fourRaw, facet, Fin.succAbove, hd.1, hd.2, bit_xor,
      show bit false = 0 from rfl, add_comm] <;> exact add_comm _ _

theorem cycle_sorted_localIndex_zero_iff {N : ℕ} (f : Fin 4 ↪o Fin N) :
    localIndex (sumInduced (cycleTournament N) 3) f.toEmbedding = 0 ↔
      decide (cycleAdj (f 0) (f 1)) ≠ decide (cycleAdj (f 2) (f 3)) ∧
      decide (cycleAdj (f 1) (f 2)) ≠ decide (cycleAdj (f 0) (f 3)) := by
  rw [localIndex_zero_iff_normalized_constant]
  simp only [normalizedFacet, cycle_sorted_facet]
  exact fourRaw_constant_iff _ _ _ _

theorem tupleVertices_four {V : Type*} [DecidableEq V] (f : Fin 4 ↪ V) :
    tupleVertices f = {f 0, f 1, f 2, f 3} := by
  unfold tupleVertices
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp

private theorem tupleVertices_perm {k : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin k ↪ V) (σ : Equiv.Perm (Fin k)) :
    tupleVertices (σ.toEmbedding.trans f) = tupleVertices f := by
  ext x
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨σ.symm i, ?_⟩
    simpa using hi

private theorem cycleQ_tuple_iff_perm {N : ℕ} (f : Fin 4 ↪ Fin N) :
    cycleQ (tupleVertices f) ↔
      ∃ σ : Equiv.Perm (Fin 4), cycleQFrame (σ.toEmbedding.trans f) := by
  constructor
  · rintro ⟨g, hg, hframe⟩
    have hv : tupleVertices f = tupleVertices g := hg.trans (tupleVertices_four g).symm
    obtain ⟨σ, hσ⟩ := tuple_perm_of_tupleVertices_eq f g hv
    exact ⟨σ, hσ.symm ▸ hframe⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.toEmbedding.trans f, ?_, hσ⟩
    rw [← tupleVertices_four, tupleVertices_perm]

private theorem cycle_sorted_cycleQ_iff {N : ℕ} (hN : 2 ≤ N) (f : Fin 4 ↪o Fin N) :
    cycleQ (tupleVertices f.toEmbedding) ↔
      decide (cycleAdj (f 0) (f 1)) ≠ decide (cycleAdj (f 2) (f 3)) ∧
      decide (cycleAdj (f 1) (f 2)) ≠ decide (cycleAdj (f 0) (f 3)) := by
  rw [cycleQ_tuple_iff_perm, ← fourQFrame_iff]
  apply exists_congr
  intro σ
  unfold cycleQFrame fourQFrame
  have htable := cycle_sorted_graph hN f
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [← htable (σ 0) (σ 1), ← htable (σ 1) (σ 2), ← htable (σ 0) (σ 2),
    ← htable (σ 0) (σ 3), ← htable (σ 1) (σ 3), ← htable (σ 2) (σ 3)]
  simp

/-- The cycle graph invariant is intrinsic to the sum-induced ternary
hypertournament; no compatibility of the vertex orders is assumed. -/
theorem cycle_localIndex_zero_iff {N : ℕ} (hN : 2 ≤ N) (f : Fin 4 ↪ Fin N) :
    localIndex (sumInduced (cycleTournament N) 3) f = 0 ↔
      cycleQ (tupleVertices f) := by
  let s := tupleVertices f
  have hs : s.card = 4 := by
    dsimp [s, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin 4 ↪o Fin N := s.orderEmbOfFin hs
  have hg : tupleVertices g.toEmbedding = s := by
    exact s.image_orderEmbOfFin_univ hs
  have hf : tupleVertices f = tupleVertices g.toEmbedding := hg.symm
  rw [localIndex_eq_of_tupleVertices_eq _ f g.toEmbedding hf,
    cycle_sorted_localIndex_zero_iff, ← cycle_sorted_cycleQ_iff hN g]
  exact congrArg cycleQ hf |>.to_iff.symm

end Hypertournaments.Antichain
