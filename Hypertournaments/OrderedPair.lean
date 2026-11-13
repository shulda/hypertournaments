import Hypertournaments.RamseyLanguage
import Hypertournaments.FinitePresentation
import Hypertournaments.PairCancellation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
Source: `tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `thm:ordering`.

# The canonical ordered pair in arity at least three

There is no n-tuple on two vertices when n >= 3, so every pair injection
preserves its hypertournament orientation. This is the pair object used
in the ordering-property argument, not a binary-arity assertion.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- The unique two-vertex n-hypertournament when n >= 3. -/
def pairModel (n : ℕ) : Hyper n (Fin 2) :=
  Hyper.fromOrderedSigns (fun _ => false)

/-- Its canonical increasing ordered expansion. -/
def orderedPairModel (n : ℕ) : Structure (orderedLanguage n) (Fin 2) :=
  toOrderedNative (pairModel n) inferInstance

/-- Any injection of a pair preserves the n-orientation in arity at least three. -/
theorem pairModel_preserves {n : ℕ} (hn : 3 ≤ n) {V : Type v}
    (A : Hyper n V) (e : Fin 2 ↪ V) : Preserves (pairModel n) A e := by
  intro t
  have hcard : n ≤ 2 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective t t.injective
  omega

/-- A pair omits every pair-cancelling forbidden family. -/
theorem pairModel_omits {n : ℕ} (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) : Omits family (pairModel n) := by
  intro m F hF e _
  have hcard : m ≤ 2 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hsize : n + 1 ≤ m := by
    simpa only [Nat.card_fin] using (hpc m F hF).2.1
  have hn := (hpc m F hF).1
  omega

/-- The native ordered pair embedding selecting any increasing pair. -/
def orderedPairEmbedding {n : ℕ} (hn : 3 ≤ n) {V : Type v}
    (A : Hyper n V) (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) :
    Embedding (orderedPairModel n) (toOrderedNative A order) := by
  let : LinearOrder V := order
  have hm : StrictMono (![x, y] : Fin 2 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  let e : Fin 2 ↪o V := OrderEmbedding.ofStrictMono ![x, y] hm
  exact @orderedEmbedding n (Fin 2) V inferInstance order (pairModel n) A e
    (pairModel_preserves hn A e.toEmbedding)

@[simp] theorem orderedPairEmbedding_zero {n : ℕ} (hn : 3 ≤ n) {V : Type v}
    (A : Hyper n V) (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : orderedPairEmbedding hn A order x y hxy 0 = x := rfl

@[simp] theorem orderedPairEmbedding_one {n : ℕ} (hn : 3 ≤ n) {V : Type v}
    (A : Hyper n V) (order : LinearOrder V) (x y : V)
    (hxy : @LT.lt V order.toLT x y) : orderedPairEmbedding hn A order x y hxy 1 = y := rfl

end Hypertournaments.Ramsey
