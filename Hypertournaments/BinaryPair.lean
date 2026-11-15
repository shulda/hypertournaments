import Hypertournaments.PairOrdering
import Hypertournaments.CanonicalOrientationRecovery
import Mathlib.Tactic.FinCases

/-!
# The two ordered edge types and the directed triangle

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
proof of the binary potential base case. The two ordered binary types must
be treated separately before the directed triangle equates their colours.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- The ordered two-vertex tournament with increasing-edge bit b. -/
def binaryPair (b : Bool) : Hyper 2 (Fin 2) := Hyper.fromOrderedSigns (fun _ => b)

def orderedBinaryPair (b : Bool) : Structure (orderedLanguage 2) (Fin 2) :=
  toOrderedNative (binaryPair b) inferInstance

/-- The actual ordered pair selecting x<y. -/
def binaryPairTuple {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : Fin 2 ↪o V := by
  let : LinearOrder V := order
  apply OrderEmbedding.ofStrictMono (![x,y] : Fin 2 → V)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem binaryPairTuple_zero {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : binaryPairTuple order x y hxy 0 = x := rfl

@[simp] theorem binaryPairTuple_one {V : Type v} (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : binaryPairTuple order x y hxy 1 = y := rfl

theorem binaryPair_preserves {V : Type v} (A : Hyper 2 V) (e : Fin 2 ↪ V)
    (b : Bool) (he : A.orient e = b) : Preserves (binaryPair b) A e := by
  apply preserves_of_canonical
  intro Q hQ
  have hmono := (Q.orderEmbOfFin hQ).strictMono.eq_id
  have ht : (Q.orderEmbOfFin hQ).toEmbedding = Function.Embedding.refl (Fin 2) := by
    ext i
    exact congrArg Fin.val (congrFun hmono i)
  rw [ht]
  have hs : (binaryPair b).orient (Function.Embedding.refl (Fin 2)) = b :=
    fromOrderedSigns_orient_strictMono (fun _ => b) _ (fun _ _ h => h)
  simpa only [Function.Embedding.refl_trans] using he.trans hs.symm

/-- Every increasing pair has its literal binary native type. -/
def binaryPairEmbedding {V : Type v} (A : Hyper 2 V) (order : LinearOrder V)
    (x y : V) (hxy : @LT.lt V order.toLT x y) (b : Bool)
    (hb : A.orient (binaryPairTuple order x y hxy).toEmbedding = b) :
    Embedding (orderedBinaryPair b) (toOrderedNative A order) :=
  @orderedEmbedding 2 (Fin 2) V inferInstance order (binaryPair b) A
    (binaryPairTuple order x y hxy)
    (binaryPair_preserves A _ b hb)

@[simp] theorem binaryPairEmbedding_zero {V : Type v} (A : Hyper 2 V) (order : LinearOrder V)
    (x y : V) (hxy : @LT.lt V order.toLT x y) (b : Bool)
    (hb : A.orient (binaryPairTuple order x y hxy).toEmbedding = b) :
    binaryPairEmbedding A order x y hxy b hb 0 = x := rfl

@[simp] theorem binaryPairEmbedding_one {V : Type v} (A : Hyper 2 V) (order : LinearOrder V)
    (x y : V) (hxy : @LT.lt V order.toLT x y) (b : Bool)
    (hb : A.orient (binaryPairTuple order x y hxy).toEmbedding = b) :
    binaryPairEmbedding A order x y hxy b hb 1 = y := rfl

/-- The increasing edge bits false,false,true form a directed triangle. -/
def binaryCycle : Hyper 2 (Fin 3) := Hyper.fromOrderedSigns (fun Q => decide (Q = {0,2}))

@[simp] theorem binaryCycle_01 :
    binaryCycle.orient (binaryPairTuple inferInstance 0 1 (by decide)).toEmbedding = false := by
  unfold binaryCycle
  rw [fromOrderedSigns_orient_strictMono _ _ (binaryPairTuple inferInstance 0 1 (by decide)).strictMono]
  decide

@[simp] theorem binaryCycle_12 :
    binaryCycle.orient (binaryPairTuple inferInstance 1 2 (by decide)).toEmbedding = false := by
  unfold binaryCycle
  rw [fromOrderedSigns_orient_strictMono _ _ (binaryPairTuple inferInstance 1 2 (by decide)).strictMono]
  decide

@[simp] theorem binaryCycle_02 :
    binaryCycle.orient (binaryPairTuple inferInstance 0 2 (by decide)).toEmbedding = true := by
  unfold binaryCycle
  rw [fromOrderedSigns_orient_strictMono _ _ (binaryPairTuple inferInstance 0 2 (by decide)).strictMono]
  decide

/-- Agreement with a new order, for a binary ordered edge of either type. -/
noncomputable def binaryPairColor {b : Bool} {V : Type v}
    {C : Structure (orderedLanguage 2) V} (order : LinearOrder V)
    (e : Embedding (orderedBinaryPair b) C) : Bool := by
  classical
  exact decide (@LT.lt V order.toLT (e 0) (e 1))

@[simp] theorem binaryPairColor_true {b : Bool} {V : Type v}
    {C : Structure (orderedLanguage 2) V} (order : LinearOrder V)
    (e : Embedding (orderedBinaryPair b) C) :
    binaryPairColor order e = true ↔ @LT.lt V order.toLT (e 0) (e 1) := by
  classical
  simp [binaryPairColor]

@[simp] theorem binaryPairColor_false {b : Bool} {V : Type v}
    {C : Structure (orderedLanguage 2) V} (order : LinearOrder V)
    (e : Embedding (orderedBinaryPair b) C) :
    binaryPairColor order e = false ↔ ¬ @LT.lt V order.toLT (e 0) (e 1) := by
  classical
  simp [binaryPairColor]

end Hypertournaments.Ramsey
