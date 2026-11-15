import Hypertournaments.CanonicalOrientationRecovery
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Lexicographic ternary masks and their intrinsic interpretation

The bits are indexed by increasing triples in lexicographic order, with the
first triple in the least significant position. A bit is read literally as
the Boolean orientation of that increasing tuple. No order-preservation is
imposed on the intrinsic embeddings.
-/

namespace Hypertournaments.FiveConstrained

/-- Pack a finite Boolean vector, least significant coordinate first. -/
def packBits : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => (f 0).toNat + 2 * packBits n (fun i => f i.succ)

@[simp] theorem packBits_testBit (n : ℕ) (f : Fin n → Bool) (i : Fin n) :
    (packBits n f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((f 0).toNat + 2 * packBits n (fun i => f i.succ)).testBit 0 = f 0
      cases f 0 <;> simp [Nat.testBit_eq_decide_div_mod_eq]
    · change ((f 0).toNat + 2 * packBits n (fun i => f i.succ)).testBit (j.val + 1) = f j.succ
      rw [Nat.testBit_add_one]
      have hdiv : ((f 0).toNat + 2 * packBits n (fun i => f i.succ)) / 2 =
          packBits n (fun i => f i.succ) := by
        cases h : f 0
        · simp
        · simp; omega
      rw [hdiv]
      exact ih (fun i => f i.succ) j

theorem packBits_lt (n : ℕ) (f : Fin n → Bool) : packBits n f < 2 ^ n := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    have ht := ih (fun i => f i.succ)
    simp only [packBits, Nat.pow_succ]
    cases f 0 <;> simp <;> omega

/-- Lexicographic rank of a pair `a < b < n`. -/
def pairRank (n a b : ℕ) : ℕ :=
  ((List.range a).map (fun i => n - i - 1)).sum + (b - a - 1)

/-- Lexicographic rank of a triple `a < b < c < n`. -/
def tripleRank (n a b c : ℕ) : ℕ :=
  ((List.range a).map (fun i => (n - i - 1).choose 2)).sum +
    ((List.range (b - a - 1)).map (fun j => n - (a + 1 + j) - 1)).sum +
    (c - b - 1)

/-- Read a triple mask on arbitrary distinct coordinates, sorting with the
appropriate sign. The values on repeated coordinates will not be used. -/
def orientAt (n mask a b c : ℕ) : Bool :=
  if a < b then
    if b < c then mask.testBit (tripleRank n a b c)
    else if a < c then !(mask.testBit (tripleRank n a c b))
    else mask.testBit (tripleRank n c a b)
  else
    if a < c then !(mask.testBit (tripleRank n b a c))
    else if b < c then mask.testBit (tripleRank n b c a)
    else !(mask.testBit (tripleRank n c b a))

theorem orientAt_swap01 (n mask a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orientAt n mask b a c = !(orientAt n mask a b c) := by
  unfold orientAt
  split_ifs <;> simp_all <;> omega

theorem orientAt_swap02 (n mask a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orientAt n mask c b a = !(orientAt n mask a b c) := by
  unfold orientAt
  split_ifs <;> simp_all <;> omega

theorem orientAt_swap12 (n mask a b c : ℕ)
    (_hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c) :
    orientAt n mask a c b = !(orientAt n mask a b c) := by
  unfold orientAt
  split_ifs <;> simp_all <;> omega

/-- The actual intrinsic ternary hypertournament represented by a mask. -/
def maskHyper (n mask : ℕ) : Hyper 3 (Fin n) where
  orient f := orientAt n mask (f 0).val (f 1).val (f 2).val
  swap_flip := by
    intro f i j hij
    have hab : (f 0).val ≠ (f 1).val := by
      intro h
      have := f.injective (Fin.ext h)
      exact (by decide : (0 : Fin 3) ≠ 1) this
    have hac : (f 0).val ≠ (f 2).val := by
      intro h
      have := f.injective (Fin.ext h)
      exact (by decide : (0 : Fin 3) ≠ 2) this
    have hbc : (f 1).val ≠ (f 2).val := by
      intro h
      have := f.injective (Fin.ext h)
      exact (by decide : (1 : Fin 3) ≠ 2) this
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at hij ⊢
    all_goals try contradiction
    all_goals simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.swap_apply_def, Fin.isValue, ↓reduceIte]
    all_goals first
      | exact orientAt_swap01 n mask _ _ _ hab hac hbc
      | exact orientAt_swap02 n mask _ _ _ hab hac hbc
      | exact orientAt_swap12 n mask _ _ _ hab hac hbc

@[simp] theorem maskHyper_orient (n mask : ℕ) (f : Fin 3 ↪ Fin n) :
    (maskHyper n mask).orient f =
      orientAt n mask (f 0).val (f 1).val (f 2).val := rfl

theorem maskHyper_orient_increasing (n mask : ℕ) (f : Fin 3 ↪ Fin n)
    (hf : StrictMono (f : Fin 3 → Fin n)) :
    (maskHyper n mask).orient f =
      mask.testBit (tripleRank n (f 0).val (f 1).val (f 2).val) := by
  have h01 : f 0 < f 1 := hf (by decide)
  have h12 : f 1 < f 2 := hf (by decide)
  simp [maskHyper, orientAt, h01, h12]

/-- An increasing tuple with explicitly supplied ordered vertices. -/
def tripleEmbedding {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    Fin 3 ↪ Fin n where
  toFun := ![a, b, c]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

@[simp] theorem tripleEmbedding_zero {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) : tripleEmbedding a b c hab hbc 0 = a := rfl

@[simp] theorem tripleEmbedding_one {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) : tripleEmbedding a b c hab hbc 1 = b := rfl

@[simp] theorem tripleEmbedding_two {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) : tripleEmbedding a b c hab hbc 2 = c := rfl

theorem tripleEmbedding_strictMono {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    StrictMono (tripleEmbedding a b c hab hbc : Fin 3 → Fin n) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [Fin.reduceFinMk, tripleEmbedding_zero, tripleEmbedding_one,
      tripleEmbedding_two] <;> omega

@[simp] theorem maskHyper_tripleEmbedding {n : ℕ} (mask : ℕ)
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    (maskHyper n mask).orient (tripleEmbedding a b c hab hbc) =
      mask.testBit (tripleRank n a.val b.val c.val) := by
  exact maskHyper_orient_increasing n mask _
    (tripleEmbedding_strictMono a b c hab hbc)

theorem preserves_iff_triples {n k : ℕ} (A : Hyper 3 (Fin n))
    (B : Hyper 3 (Fin k)) (e : Fin n ↪ Fin k) :
    Preserves A B e ↔
      ∀ (a b c : Fin n) (hab : a < b) (hbc : b < c),
        B.orient ((tripleEmbedding a b c hab hbc).trans e) =
          A.orient (tripleEmbedding a b c hab hbc) := by
  constructor
  · intro h a b c hab hbc
    exact h _
  · intro h
    apply preserves_of_canonical A B e
    intro Q hQ
    let f := (Q.orderEmbOfFin hQ).toEmbedding
    have hf : StrictMono (f : Fin 3 → Fin n) := (Q.orderEmbOfFin hQ).strictMono
    have heq : tripleEmbedding (f 0) (f 1) (f 2)
        (hf (by decide)) (hf (by decide)) = f := by
      ext i
      fin_cases i <;> rfl
    simpa only [heq] using h (f 0) (f 1) (f 2) (hf (by decide)) (hf (by decide))

/-- The subset table of the mask. Wrong-cardinality sets have a dummy value. -/
def maskSigns (n mask : ℕ) (Q : Finset (Fin n)) : Bool :=
  if hQ : Q.card = 3 then
    let f := Q.orderEmbOfFin hQ
    mask.testBit (tripleRank n (f 0).val (f 1).val (f 2).val)
  else false

/-- The direct six-case evaluator agrees with the pre-existing canonical
sign-table construction on every intrinsic tuple. -/
theorem maskHyper_fromOrderedSigns_orient (n mask : ℕ) (f : Fin 3 ↪ Fin n) :
    (maskHyper n mask).orient f =
      (Hyper.fromOrderedSigns (maskSigns n mask)).orient f := by
  apply orientations_equal_of_canonical
  intro Q hQ
  have hvertices : tupleVertices (Q.orderEmbOfFin hQ).toEmbedding = Q := by
    exact Finset.image_orderEmbOfFin_univ Q hQ
  rw [maskHyper_orient_increasing n mask _ (Q.orderEmbOfFin hQ).strictMono,
    fromOrderedSigns_orient_strictMono (maskSigns n mask) _
      (Q.orderEmbOfFin hQ).strictMono, hvertices]
  simp [maskSigns, hQ]

/-- Equality on increasing-triple bits determines every tuple orientation. -/
theorem maskHyper_orient_eq_of_bits {n : ℕ} (m k : ℕ)
    (h : ∀ (a b c : Fin n), a < b → b < c →
      m.testBit (tripleRank n a.val b.val c.val) =
        k.testBit (tripleRank n a.val b.val c.val)) :
    ∀ f, (maskHyper n m).orient f = (maskHyper n k).orient f := by
  have hp : Preserves (maskHyper n k) (maskHyper n m) (Function.Embedding.refl _) := by
    apply (preserves_iff_triples _ _ _).mpr
    intro a b c hab hbc
    simp only [Function.Embedding.trans_refl, maskHyper_tripleEmbedding]
    exact h a b c hab hbc
  exact hp


def tripleEntries (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      ((List.range n).filter (fun c => a < b && b < c)).map (fun c => (a,b,c))

def lookupTriple (n i : ℕ) : ℕ × ℕ × ℕ :=
  ((tripleEntries n).find? (fun t => tripleRank n t.1 t.2.1 t.2.2 == i)).getD (0,0,0)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem lookupTriple_correct_small : ∀ n : Fin 10, ∀ a b c : Fin n.val,
    a < b → b < c →
      lookupTriple n.val (tripleRank n.val a.val b.val c.val) = (a.val,b.val,c.val) ∧
      tripleRank n.val a.val b.val c.val < n.val.choose 3 := by decide

/-- Read an arbitrary intrinsic structure on a valid increasing triple. -/
def tripleValue {n : ℕ} (A : Hyper 3 (Fin n)) (t : ℕ × ℕ × ℕ) : Bool :=
  if h : t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 then
    A.orient (tripleEmbedding ⟨t.1,h.1⟩ ⟨t.2.1,h.2.1⟩ ⟨t.2.2,h.2.2.1⟩
      h.2.2.2.1 h.2.2.2.2)
  else false

/-- A lexicographic integer presentation of an arbitrary finite intrinsic
ternary structure. The lookup correctness theorem below is needed only up to
nine vertices, the maximum size of a retained certificate union. -/
def maskOfHyper {n : ℕ} (A : Hyper 3 (Fin n)) : ℕ :=
  packBits (n.choose 3) (fun i => tripleValue A (lookupTriple n i.val))

theorem maskOfHyper_lt {n : ℕ} (A : Hyper 3 (Fin n)) :
    maskOfHyper A < 2 ^ (n.choose 3) := packBits_lt _ _

theorem maskOfHyper_testBit {n : ℕ} (hn : n ≤ 9) (A : Hyper 3 (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    (maskOfHyper A).testBit (tripleRank n a.val b.val c.val) =
      A.orient (tripleEmbedding a b c hab hbc) := by
  have hsmall := lookupTriple_correct_small ⟨n,by omega⟩ a b c hab hbc
  let i : Fin (n.choose 3) := ⟨tripleRank n a.val b.val c.val, hsmall.2⟩
  have hp := packBits_testBit (n.choose 3)
    (fun j => tripleValue A (lookupTriple n j.val)) i
  change (maskOfHyper A).testBit (tripleRank n a.val b.val c.val) = _ at hp
  rw [hp, hsmall.1]
  simp [tripleValue, a.isLt, b.isLt, c.isLt, hab, hbc]

theorem maskHyper_maskOfHyper_orient {n : ℕ} (hn : n ≤ 9)
    (A : Hyper 3 (Fin n)) (f : Fin 3 ↪ Fin n) :
    (maskHyper n (maskOfHyper A)).orient f = A.orient f := by
  have hp : Preserves A (maskHyper n (maskOfHyper A)) (Function.Embedding.refl _) := by
    apply (preserves_iff_triples _ _ _).mpr
    intro a b c hab hbc
    simp only [Function.Embedding.trans_refl, maskHyper_tripleEmbedding]
    exact maskOfHyper_testBit hn A a b c hab hbc
  exact hp f

/-- Literal preservation for the recovered finite integer presentation. -/
theorem maskHyper_maskOfHyper_preserves {n : ℕ} (hn : n ≤ 9)
    (A : Hyper 3 (Fin n)) :
    Preserves A (maskHyper n (maskOfHyper A)) (Function.Embedding.refl _) := by
  intro f
  exact maskHyper_maskOfHyper_orient hn A f


/-- Pack any Boolean table on increasing triples in lexicographic order. -/
def maskOfTripleFunction (n : ℕ) (f : ℕ → ℕ → ℕ → Bool) : ℕ :=
  packBits (n.choose 3) (fun i =>
    let t := lookupTriple n i.val
    f t.1 t.2.1 t.2.2)

theorem maskOfTripleFunction_lt (n : ℕ) (f : ℕ → ℕ → ℕ → Bool) :
    maskOfTripleFunction n f < 2 ^ (n.choose 3) := packBits_lt _ _

theorem maskOfTripleFunction_testBit {n : ℕ} (hn : n ≤ 9)
    (f : ℕ → ℕ → ℕ → Bool)
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    (maskOfTripleFunction n f).testBit (tripleRank n a.val b.val c.val) =
      f a.val b.val c.val := by
  have hsmall := lookupTriple_correct_small ⟨n,by omega⟩ a b c hab hbc
  let i : Fin (n.choose 3) := ⟨tripleRank n a.val b.val c.val, hsmall.2⟩
  have hp := packBits_testBit (n.choose 3)
    (fun j => let t := lookupTriple n j.val; f t.1 t.2.1 t.2.2) i
  change (maskOfTripleFunction n f).testBit (tripleRank n a.val b.val c.val) = _ at hp
  rw [hp, hsmall.1]

end Hypertournaments.FiveConstrained
