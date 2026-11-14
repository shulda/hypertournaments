import Hypertournaments.FiveConstrained.Catalogue
import Hypertournaments.FiveConstrained.Mask
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Hypertournaments.FiveConstrained

private def first5 : Fin 10 → Fin 5 := ![0,0,0,0,0,0,1,1,1,2]
private def middle5 : Fin 10 → Fin 5 := ![1,1,1,2,2,3,2,2,3,3]
private def last5 : Fin 10 → Fin 5 := ![2,3,4,3,4,4,3,4,4,4]

/-- The ten increasing triples of five vertices, in lexicographic order. -/
def triple5 (i : Fin 10) : Fin 3 ↪ Fin 5 :=
  tripleEmbedding (first5 i) (middle5 i) (last5 i)
    (by
      have h : ∀ j : Fin 10, first5 j < middle5 j := by decide
      exact h i)
    (by
      have h : ∀ j : Fin 10, middle5 j < last5 j := by decide
      exact h i)

/-- Every increasing three-tuple occurs in the lexicographic list. -/
theorem triple5_complete (a b c : Fin 5) (hab : a < b) (hbc : b < c) :
    ∃ i : Fin 10, triple5 i = tripleEmbedding a b c hab hbc := by
  have h : ∀ a b c : Fin 5, a < b → b < c →
      ∃ i : Fin 10, first5 i = a ∧ middle5 i = b ∧ last5 i = c := by decide
  obtain ⟨i, hi, hj, hk⟩ := h a b c hab hbc
  refine ⟨i, ?_⟩
  ext k
  fin_cases k <;> simp [triple5, hi, hj, hk]

/-- Encode an actual intrinsic five-vertex ternary hypertournament. -/
def encode5 (A : Hyper 3 (Fin 5)) : ℕ := packBits 10 fun i => A.orient (triple5 i)

theorem encode5_lt (A : Hyper 3 (Fin 5)) : encode5 A < 1024 :=
  packBits_lt 10 _

theorem encode5_bit (A : Hyper 3 (Fin 5)) (i : Fin 10) :
    (encode5 A).testBit i.val = A.orient (triple5 i) := packBits_testBit 10 _ i

theorem triple5_rank : ∀ i : Fin 10,
    tripleRank 5 (first5 i).val (middle5 i).val (last5 i).val = i.val := by decide

@[simp] theorem maskHyper_triple5 (m : ℕ) (i : Fin 10) :
    (maskHyper 5 m).orient (triple5 i) = m.testBit i.val := by
  change (maskHyper 5 m).orient
    (tripleEmbedding (first5 i) (middle5 i) (last5 i) _ _) = _
  rw [maskHyper_tripleEmbedding, triple5_rank]

/-- Decoding an encoded intrinsic object recovers every tuple orientation. -/
theorem maskHyper_encode5 (A : Hyper 3 (Fin 5)) :
    ∀ t, (maskHyper 5 (encode5 A)).orient t = A.orient t := by
  have h : Preserves A (maskHyper 5 (encode5 A)) (Function.Embedding.refl _) := by
    apply (preserves_iff_triples _ _ _).mpr
    intro a b c hab hbc
    obtain ⟨i, hi⟩ := triple5_complete a b c hab hbc
    simpa only [← hi, Function.Embedding.trans_refl, maskHyper_triple5] using encode5_bit A i
  exact h

/-- Ten-bit masks are exactly recovered by the intrinsic encoder. -/
theorem encode5_maskHyper : ∀ m : Fin 1024, encode5 (maskHyper 5 m.val) = m.val := by
  intro m
  unfold encode5
  simp only [maskHyper_triple5]
  have h : ∀ m : Fin 1024, packBits 10 (fun i : Fin 10 => m.val.testBit i.val) = m.val := by
    decide
  exact h m

end Hypertournaments.FiveConstrained
