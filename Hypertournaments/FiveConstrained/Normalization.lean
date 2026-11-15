import Hypertournaments.FiveConstrained.Classes
import Hypertournaments.LocalTypeRealization
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Normalization of four/five palettes

Ordinary AP implies JEP. In an unbounded class this forces every admitted
four-vertex structure to occur in an admitted five-packet. The converse
support inclusion is the consistency condition on the prescribed palettes.
-/

namespace Hypertournaments.FiveConstrained

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem support4_correct_fin : ∀ (t : Fin 12) (d : Fin 3),
    (support4 t).testBit d.val = true ↔
      ∃ i : Fin 5, localIndex (maskHyper 5 (representative t)) (Fin.succAboveEmb i) = d.val := by
  decide

theorem exists_localIndex_succAbove (A : Hyper 3 (Fin 5))
    (e : Fin 4 ↪ Fin 5) :
    ∃ i : Fin 5, localIndex A (Fin.succAboveEmb i) = localIndex A e := by
  classical
  have hmiss : ∃ i : Fin 5, i ∉ Set.range e := by
    by_contra! h
    have hcard := Fintype.card_le_of_surjective (e : Fin 4 → Fin 5) h
    simp at hcard
  obtain ⟨i, hi⟩ := hmiss
  have hpre (x : Fin 4) : ∃ j : Fin 4, i.succAbove j = e x := by
    have hmem : e x ∈ Set.range i.succAbove := by
      rw [Fin.range_succAbove]
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx
      exact hi ⟨x, hx⟩
    exact hmem
  choose f hf using hpre
  have hfinj : Function.Injective f := by
    intro x y h
    apply e.injective
    rw [← hf x, ← hf y, h]
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective f
    ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have heq : σ.toEmbedding.trans (Fin.succAboveEmb i) = e := by
    ext x
    exact congrArg Fin.val (hf x)
  refine ⟨i, ?_⟩
  have hidx := localIndex_perm_all A (Fin.succAboveEmb i) σ
  rw [heq] at hidx
  exact hidx.symm

theorem support4_correct (t : Fin 12) {d : ℕ} (hd : d ≤ 2) :
    (support4 t).testBit d = true ↔
      ∃ e : Fin 4 ↪ Fin 5, localIndex (maskHyper 5 (representative t)) e = d := by
  rw [support4_correct_fin t ⟨d, by omega⟩]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Fin.succAboveEmb i, hi⟩
  · rintro ⟨e, he⟩
    obtain ⟨i, hi⟩ := exists_localIndex_succAbove (maskHyper 5 (representative t)) e
    exact ⟨i, hi.trans he⟩

private theorem supportFold_testBit (palette d : ℕ) (ts : List (Fin 12)) (initial : ℕ) :
    ((ts.foldl (fun mask t =>
      if palette.testBit t.val then mask ||| support4 t else mask) initial).testBit d = true) ↔
      initial.testBit d = true ∨
        ∃ t ∈ ts, palette.testBit t.val = true ∧ (support4 t).testBit d = true := by
  induction ts generalizing initial with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih]
    by_cases ht : palette.testBit t.val = true
    · simp [ht, Nat.testBit_or, or_assoc]
    · have hf : palette.testBit t.val = false := Bool.eq_false_iff.mpr ht
      simp [hf]

theorem certificateSupport4_testBit_iff (palette d : ℕ) :
    (certificateSupport4 palette).testBit d = true ↔
      ∃ t : Fin 12, palette.testBit t.val = true ∧ (support4 t).testBit d = true := by
  unfold certificateSupport4
  rw [supportFold_testBit]
  simp

theorem PacketAllowed.admissible_normalized {palette : ℕ}
    {A : Hyper 3 (Fin 5)} (hA : PacketAllowed palette A) :
    Admissible (fourPalette (certificateSupport4 palette)) A := by
  obtain ⟨t, ht, σ, hσ⟩ := hA
  intro e
  have hd : localIndex A e ≤ 2 := localIndex_le_central A e
  apply (certificateSupport4_testBit_iff palette (localIndex A e)).mpr
  refine ⟨t, ht, (support4_correct t hd).mpr ?_⟩
  let f : Fin 4 ↪ Fin 5 := e.trans σ.symm.toEmbedding
  have heq : f.trans σ.toEmbedding = e := by
    ext x
    simp [f]
  refine ⟨f, ?_⟩
  have h := localIndex_preserves _ _ _ hσ f
  simpa only [heq] using h

theorem packetAllowed_representative (palette : ℕ) (t : Fin 12)
    (ht : palette.testBit t.val = true) :
    PacketAllowed palette (maskHyper 5 (representative t)) := by
  exact ⟨t, ht, 1, fun _ => rfl⟩

/-- Prescribed five-types must satisfy the separately prescribed four-condition. -/
def Consistent (four five : ℕ) : Prop :=
  ∀ t : Fin 12, five.testBit t.val = true →
    Admissible (fourPalette four) (maskHyper 5 (representative t))

theorem normalized_consistent (palette : ℕ) :
    Consistent (certificateSupport4 palette) palette := by
  intro t ht
  exact (packetAllowed_representative palette t ht).admissible_normalized

theorem normalization_of_hasAP {four five : ℕ}
    (hconsistent : Consistent four five)
    (hU : (constrainedClass four five).Unbounded)
    (hAP : (constrainedClass four five).HasAP) :
    ∀ d : ℕ, d ≤ 2 →
      (four.testBit d = true ↔ (certificateSupport4 five).testBit d = true) := by
  intro d hd
  constructor
  · intro hfour
    obtain ⟨A, hidx⟩ := exists_localIndex_eq (n := 3) (d := d) hd
    have hA : constrainedClass four five 4 A := by
      refine ⟨(packet_admissible_iff_localIndex_mem (fourPalette four) A).mpr ?_, ?_⟩
      · simpa [hidx, fourPalette] using hfour
      · intro e
        have hcard := Fintype.card_le_of_injective e e.injective
        simp at hcard
    obtain ⟨B, hB, hAB⟩ :=
      (constrainedClass_hasJEP_of_hasAP hAP).exists_onePoint_extension
        (constrainedClass_hereditary four five) hU A hA
    obtain ⟨t, ht, σ, hσ⟩ := hB.2 (Function.Embedding.refl _)
    apply (certificateSupport4_testBit_iff five d).mpr
    refine ⟨t, ht, (support4_correct t hd).mpr ?_⟩
    let e : Fin 4 ↪ Fin 5 :=
      (onePointBaseEmbedding 4).trans σ.symm.toEmbedding
    have heq : e.trans σ.toEmbedding = onePointBaseEmbedding 4 := by
      ext x
      simp [e]
    refine ⟨e, ?_⟩
    calc
      localIndex (maskHyper 5 (representative t)) e =
          localIndex B (e.trans σ.toEmbedding) := by
        exact localIndex_preserves _ _ _ hσ e
      _ = localIndex B (onePointBaseEmbedding 4) := by rw [heq]
      _ = localIndex A (Function.Embedding.refl _) :=
        (localIndex_preserves A B (onePointBaseEmbedding 4) hAB
          (Function.Embedding.refl _)).symm
      _ = d := hidx
  · intro hsupp
    obtain ⟨t, ht, htd⟩ := (certificateSupport4_testBit_iff five d).mp hsupp
    obtain ⟨e, he⟩ := (support4_correct t hd).mp htd
    simpa [fourPalette, he] using hconsistent t ht e

/-- The normalization changes no actual finite member of an unbounded AP class. -/
theorem constrainedClass_iff_normalized_of_hasAP {four five : ℕ}
    (hconsistent : Consistent four five)
    (hU : (constrainedClass four five).Unbounded)
    (hAP : (constrainedClass four five).HasAP)
    {V : Type*} (A : Hyper 3 V) :
    Constrained four five A ↔
      Constrained (certificateSupport4 five) five A := by
  have hn := normalization_of_hasAP hconsistent hU hAP
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro e
    exact (hn (localIndex A e) (localIndex_le_central A e)).mp (h.1 e)
  · intro h
    refine ⟨?_, h.2⟩
    intro e
    exact (hn (localIndex A e) (localIndex_le_central A e)).mpr (h.1 e)

end Hypertournaments.FiveConstrained
