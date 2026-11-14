import Hypertournaments.FiveConstrained.CertificatesBasic
import Hypertournaments.FiveConstrained.Mask
import Hypertournaments.OnePointJoint
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Actual intrinsic structures underlying one-point certificates

The executable side and mixed bits are realized by genuine `Hyper`
structures. The auxiliary ordinal order is used only to specify canonical
increasing triples; every preservation statement concerns all tuples.
-/

namespace Hypertournaments.FiveConstrained

private def tableOrient (s : ℕ → ℕ → ℕ → Bool) (a b c : ℕ) : Bool :=
  if a < b then
    if b < c then s a b c
    else if a < c then !(s a c b)
    else s c a b
  else
    if a < c then !(s b a c)
    else if b < c then s b c a
    else !(s c b a)

private theorem tableOrient_swap01 (s : ℕ → ℕ → ℕ → Bool) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tableOrient s b a c = !(tableOrient s a b c) := by
  unfold tableOrient
  split_ifs <;> simp_all <;> omega

private theorem tableOrient_swap02 (s : ℕ → ℕ → ℕ → Bool) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tableOrient s c b a = !(tableOrient s a b c) := by
  unfold tableOrient
  split_ifs <;> simp_all <;> omega

private theorem tableOrient_swap12 (s : ℕ → ℕ → ℕ → Bool) (a b c : ℕ)
    (_hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c) :
    tableOrient s a c b = !(tableOrient s a b c) := by
  unfold tableOrient
  split_ifs <;> simp_all <;> omega

private def tableHyper (n : ℕ) (s : ℕ → ℕ → ℕ → Bool) : Hyper 3 (Fin n) where
  orient f := tableOrient s (f 0).val (f 1).val (f 2).val
  swap_flip := by
    intro f i j hij
    have hab : (f 0).val ≠ (f 1).val := by
      intro h
      exact (by decide : (0 : Fin 3) ≠ 1) (f.injective (Fin.ext h))
    have hac : (f 0).val ≠ (f 2).val := by
      intro h
      exact (by decide : (0 : Fin 3) ≠ 2) (f.injective (Fin.ext h))
    have hbc : (f 1).val ≠ (f 2).val := by
      intro h
      exact (by decide : (1 : Fin 3) ≠ 2) (f.injective (Fin.ext h))
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at hij ⊢
    all_goals try contradiction
    all_goals simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.swap_apply_def, Fin.isValue, ↓reduceIte]
    all_goals first
      | exact tableOrient_swap01 s _ _ _ hab hac hbc
      | exact tableOrient_swap02 s _ _ _ hab hac hbc
      | exact tableOrient_swap12 s _ _ _ hab hac hbc

private theorem tableHyper_orient_increasing (n : ℕ)
    (s : ℕ → ℕ → ℕ → Bool) (f : Fin 3 ↪ Fin n)
    (hf : StrictMono (f : Fin 3 → Fin n)) :
    (tableHyper n s).orient f = s (f 0).val (f 1).val (f 2).val := by
  have h01 : f 0 < f 1 := hf (by decide)
  have h12 : f 1 < f 2 := hf (by decide)
  simp [tableHyper, tableOrient, h01, h12]

namespace CertificateDiagram

def baseHyper (d : CertificateDiagram) : Hyper 3 (Fin d.baseSize) :=
  maskHyper d.baseSize d.base

def sideHyper (d : CertificateDiagram) (rightSide : Bool) :
    Hyper 3 (Fin (d.baseSize + 1)) :=
  tableHyper (d.baseSize + 1) (d.sideBit rightSide)

theorem sideHyper_orient_increasing (d : CertificateDiagram) (rightSide : Bool)
    (f : Fin 3 ↪ Fin (d.baseSize + 1))
    (hf : StrictMono (f : Fin 3 → Fin (d.baseSize + 1))) :
    (d.sideHyper rightSide).orient f =
      d.sideBit rightSide (f 0).val (f 1).val (f 2).val :=
  tableHyper_orient_increasing _ _ f hf

theorem base_side (d : CertificateDiagram) (rightSide : Bool) :
    Preserves d.baseHyper (d.sideHyper rightSide) (onePointBaseEmbedding d.baseSize) := by
  apply (preserves_iff_triples _ _ _).mpr
  intro a b c hab hbc
  have hf := tripleEmbedding_strictMono a b c hab hbc
  have hmap : StrictMono (fun i =>
      onePointBaseEmbedding d.baseSize (tripleEmbedding a b c hab hbc i)) := by
    intro i j hij
    exact hf hij
  rw [sideHyper_orient_increasing _ _ _ hmap]
  change d.sideBit rightSide a.val b.val c.val = _
  unfold baseHyper
  rw [maskHyper_tripleEmbedding]
  simp [sideBit, c.isLt, tripleRank, certificateTripleRank]

/-- A different actual pair-link bit already prevents identification of
the two added points in an ordinary amalgam. -/
theorem side_disagree_of_pair (d : CertificateDiagram)
    (a b : Fin d.baseSize) (hab : a < b)
    (hbit : d.left.testBit (certificatePairRank d.baseSize a.val b.val) ≠
      d.right.testBit (certificatePairRank d.baseSize a.val b.val)) :
    ∃ t : Fin 3 ↪ Fin (d.baseSize + 1),
      (d.sideHyper false).orient t ≠ (d.sideHyper true).orient t := by
  let t := tripleEmbedding a.castSucc b.castSucc (Fin.last d.baseSize) hab b.isLt
  have ht := tripleEmbedding_strictMono a.castSucc b.castSucc
    (Fin.last d.baseSize) hab b.isLt
  refine ⟨t, ?_⟩
  rw [sideHyper_orient_increasing _ _ _ ht, sideHyper_orient_increasing _ _ _ ht]
  simpa [t, sideBit] using hbit

private theorem different_bit_below (k left right : ℕ)
    (hl : left < 2 ^ k) (hr : right < 2 ^ k) (hne : left ≠ right) :
    ∃ i : Fin k, left.testBit i.val ≠ right.testBit i.val := by
  classical
  by_contra h
  have hsame (i : Fin k) : left.testBit i.val = right.testBit i.val := by
    by_contra hi
    exact h ⟨i, hi⟩
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact hsame ⟨i, hi⟩
  · have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hl hpow),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hr hpow)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem pair_rank_covers_small :
    ∀ m : Fin 8, ∀ i : Fin (m.val.choose 2),
      ∃ a b : Fin m.val, a < b ∧ certificatePairRank m.val a.val b.val = i.val := by
  decide

/-- The integer inequality used by the finite checker entails actual side
disagreement once the link masks are bounded. All retained certificates
have base size at most seven. -/
theorem side_disagree (d : CertificateDiagram) (hm : d.baseSize ≤ 7)
    (hl : d.left < 2 ^ (d.baseSize.choose 2))
    (hr : d.right < 2 ^ (d.baseSize.choose 2)) (hne : d.left ≠ d.right) :
    ∃ t : Fin 3 ↪ Fin (d.baseSize + 1),
      (d.sideHyper false).orient t ≠ (d.sideHyper true).orient t := by
  obtain ⟨i, hi⟩ := different_bit_below _ _ _ hl hr hne
  obtain ⟨a, b, hab, hrank⟩ := pair_rank_covers_small ⟨d.baseSize, by omega⟩ i
  apply side_disagree_of_pair d a b hab
  simpa [hrank] using hi

/-- Increasing-triple bits of the canonical union. -/
def jointBit (d : CertificateDiagram) (x a b c : ℕ) : Bool :=
  if c < d.baseSize + 1 then d.sideBit false a b c
  else if b < d.baseSize then d.sideBit true a b c
  else x.testBit a

def jointHyper (d : CertificateDiagram) (x : ℕ) : Hyper 3 (Fin (d.baseSize + 2)) :=
  tableHyper (d.baseSize + 2) (d.jointBit x)

theorem jointHyper_orient_increasing (d : CertificateDiagram) (x : ℕ)
    (f : Fin 3 ↪ Fin (d.baseSize + 2))
    (hf : StrictMono (f : Fin 3 → Fin (d.baseSize + 2))) :
    (d.jointHyper x).orient f =
      d.jointBit x (f 0).val (f 1).val (f 2).val :=
  tableHyper_orient_increasing _ _ f hf

theorem joint_left (d : CertificateDiagram) (x : ℕ) :
    Preserves (d.sideHyper false) (d.jointHyper x) (leftJointInclusion d.baseSize) := by
  apply (preserves_iff_triples _ _ _).mpr
  intro a b c hab hbc
  have hf := tripleEmbedding_strictMono a b c hab hbc
  have hmap : StrictMono (fun i =>
      leftJointInclusion d.baseSize (tripleEmbedding a b c hab hbc i)) := by
    intro i j hij
    exact hf hij
  rw [jointHyper_orient_increasing _ _ _ hmap, sideHyper_orient_increasing _ _ _ hf]
  change d.jointBit x a.val b.val c.val = d.sideBit false a.val b.val c.val
  simp [jointBit, c.isLt]

private theorem rightJointInclusion_val (m : ℕ) (i : Fin (m + 1)) :
    (rightJointInclusion m i).val = if i.val < m then i.val else m + 1 := by
  rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · rw [rightJointInclusion_old]
    simp [j.isLt]
  · rw [rightJointInclusion_new]
    simp

private theorem rightJointInclusion_strictMono (m : ℕ) :
    StrictMono (rightJointInclusion m : Fin (m + 1) → Fin (m + 2)) := by
  exact (Fin.succAboveOrderEmb (Fin.castSucc (Fin.last m))).strictMono

theorem joint_right (d : CertificateDiagram) (x : ℕ) :
    Preserves (d.sideHyper true) (d.jointHyper x) (rightJointInclusion d.baseSize) := by
  apply (preserves_iff_triples _ _ _).mpr
  intro a b c hab hbc
  have hf := tripleEmbedding_strictMono a b c hab hbc
  have hmap := (rightJointInclusion_strictMono d.baseSize).comp hf
  rw [jointHyper_orient_increasing _ _ _ hmap, sideHyper_orient_increasing _ _ _ hf]
  change d.jointBit x (rightJointInclusion d.baseSize a).val
      (rightJointInclusion d.baseSize b).val (rightJointInclusion d.baseSize c).val =
    d.sideBit true a.val b.val c.val
  have ha : a.val < d.baseSize := by have := c.isLt; change a.val < b.val at hab; change b.val < c.val at hbc; omega
  have hb : b.val < d.baseSize := by have := c.isLt; change b.val < c.val at hbc; omega
  rw [rightJointInclusion_val, rightJointInclusion_val, rightJointInclusion_val]
  simp only [ha, hb, ↓reduceIte]
  by_cases hc : c.val < d.baseSize
  · simp [hc, jointBit, sideBit, show c.val < d.baseSize + 1 by omega]
  · have hcEq : c.val = d.baseSize := by have := c.isLt; omega
    simp [hcEq, jointBit, sideBit, hb]

/-- The mixed triple at one base point, in increasing order. -/
def mixedTuple (d : CertificateDiagram) (a : Fin d.baseSize) :
    Fin 3 ↪ Fin (d.baseSize + 2) :=
  tripleEmbedding a.castSucc.castSucc (Fin.last d.baseSize).castSucc
    (Fin.last (d.baseSize + 1)) (by exact a.isLt) (by simp)

theorem mixedTuple_strictMono (d : CertificateDiagram) (a : Fin d.baseSize) :
    StrictMono (d.mixedTuple a : Fin 3 → Fin (d.baseSize + 2)) :=
  tripleEmbedding_strictMono _ _ _ _ _

theorem joint_mixed (d : CertificateDiagram) (x : ℕ) (a : Fin d.baseSize) :
    (d.jointHyper x).orient (d.mixedTuple a) = x.testBit a.val := by
  rw [jointHyper_orient_increasing _ _ _ (mixedTuple_strictMono d a)]
  simp [mixedTuple, jointBit]

/-- Read exactly the as-yet unknown mixed orientations of an actual joint. -/
def mixedMask (d : CertificateDiagram) (E : Hyper 3 (Fin (d.baseSize + 2))) : ℕ :=
  packBits d.baseSize (fun a => E.orient (d.mixedTuple a))

theorem mixedMask_lt (d : CertificateDiagram) (E : Hyper 3 (Fin (d.baseSize + 2))) :
    d.mixedMask E < 2 ^ d.baseSize := packBits_lt _ _

theorem mixedMask_testBit (d : CertificateDiagram) (E : Hyper 3 (Fin (d.baseSize + 2)))
    (a : Fin d.baseSize) : (d.mixedMask E).testBit a.val = E.orient (d.mixedTuple a) :=
  packBits_testBit _ _ _

/-- Any actual canonical joint is recovered from its prescribed sides and
the finitely many mixed bits. This is an equality on every ordered tuple,
not merely on the increasing presentation. -/
theorem joint_recovery (d : CertificateDiagram) (E : Hyper 3 (Fin (d.baseSize + 2)))
    (hL : Preserves (d.sideHyper false) E (leftJointInclusion d.baseSize))
    (hR : Preserves (d.sideHyper true) E (rightJointInclusion d.baseSize)) :
    ∀ f, E.orient f = (d.jointHyper (d.mixedMask E)).orient f := by
  have hp : Preserves (d.jointHyper (d.mixedMask E)) E (Function.Embedding.refl _) := by
    apply (preserves_iff_triples _ _ _).mpr
    intro a b c hab hbc
    rw [Function.Embedding.trans_refl,
      jointHyper_orient_increasing _ _ _ (tripleEmbedding_strictMono a b c hab hbc)]
    change E.orient (tripleEmbedding a b c hab hbc) =
      d.jointBit (d.mixedMask E) a.val b.val c.val
    have ha_lt : a.val < b.val := hab
    have hb_lt : b.val < c.val := hbc
    by_cases hc : c.val < d.baseSize + 1
    · let a' : Fin (d.baseSize + 1) := ⟨a.val, by omega⟩
      let b' : Fin (d.baseSize + 1) := ⟨b.val, by omega⟩
      let c' : Fin (d.baseSize + 1) := ⟨c.val, hc⟩
      have hab' : a' < b' := hab
      have hbc' : b' < c' := hbc
      have heq : (tripleEmbedding a' b' c' hab' hbc').trans
          (leftJointInclusion d.baseSize) = tripleEmbedding a b c hab hbc := by
        ext i
        fin_cases i <;> rfl
      have h := hL (tripleEmbedding a' b' c' hab' hbc')
      rw [heq, sideHyper_orient_increasing _ _ _
        (tripleEmbedding_strictMono a' b' c' hab' hbc')] at h
      simpa [jointBit, hc, a', b', c'] using h
    · have hcEq : c.val = d.baseSize + 1 := by have := c.isLt; omega
      by_cases hb : b.val < d.baseSize
      · have ha : a.val < d.baseSize := by omega
        let a' : Fin (d.baseSize + 1) := ⟨a.val, by omega⟩
        let b' : Fin (d.baseSize + 1) := ⟨b.val, by omega⟩
        let c' : Fin (d.baseSize + 1) := Fin.last d.baseSize
        have hab' : a' < b' := hab
        have hbc' : b' < c' := hb
        have heq : (tripleEmbedding a' b' c' hab' hbc').trans
            (rightJointInclusion d.baseSize) = tripleEmbedding a b c hab hbc := by
          apply Function.Embedding.ext
          intro i
          fin_cases i
          · apply Fin.ext
            change (rightJointInclusion d.baseSize a').val = a.val
            simp [rightJointInclusion_val, a', ha]
          · apply Fin.ext
            change (rightJointInclusion d.baseSize b').val = b.val
            simp [rightJointInclusion_val, b', hb]
          · apply Fin.ext
            change (rightJointInclusion d.baseSize c').val = c.val
            simp [rightJointInclusion_val, c', hcEq]
        have h := hR (tripleEmbedding a' b' c' hab' hbc')
        rw [heq, sideHyper_orient_increasing _ _ _
          (tripleEmbedding_strictMono a' b' c' hab' hbc')] at h
        simpa [jointBit, hc, hb, sideBit, hcEq, a', b', c'] using h
      · have hbEq : b.val = d.baseSize := by omega
        have ha : a.val < d.baseSize := by omega
        let a' : Fin d.baseSize := ⟨a.val, ha⟩
        have heq : tripleEmbedding a b c hab hbc = d.mixedTuple a' := by
          apply Function.Embedding.ext
          intro i
          fin_cases i
          · rfl
          · exact Fin.ext hbEq
          · exact Fin.ext hcEq
        rw [heq]
        simpa [jointBit, hc, hb, a'] using (mixedMask_testBit d E a').symm
  exact hp

end CertificateDiagram

end Hypertournaments.FiveConstrained
