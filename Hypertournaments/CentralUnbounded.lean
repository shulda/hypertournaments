import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.AllArityCanonicalAdmissibility
import Hypertournaments.TwoPadPacketCount
import CCO.UnaryHN.OrderedAmbient

/-!
# Central local type and unbounded finite admissible structures

Constant canonical orientations give admissible structures of arbitrary
size when the central type is allowed. Conversely, finite Ramsey for
pure linear orders supplies a constant raw packet inside any sufficiently
large hypertournament. Its actual local index is the central one.

The Ramsey input below is the existing proved theorem on the empty base
language; no Ramsey assumption about the admissible class is made.
-/

namespace Hypertournaments

/-- The finite admissible structures have arbitrarily large cardinalities. -/
def UnboundedAdmissible (n : ℕ) (S : Set ℕ) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ A : Hyper n (Fin m), Admissible S A

private theorem constantRawPacket_count (k : ℕ) (b : Bool) :
    boolPacketPositiveCount (fun i : Fin k =>
      Bool.xor b (decide (i.val % 2 = 1))) =
        if b then k - k / 2 else k / 2 := by
  induction k generalizing b with
  | zero => simp [boolPacketPositiveCount]
  | succ k ih =>
    have htail (i : Fin k) :
        Bool.xor b (decide (i.succ.val % 2 = 1)) =
          Bool.xor (!b) (decide (i.val % 2 = 1)) := by
      have hpar : decide (i.succ.val % 2 = 1) = !decide (i.val % 2 = 1) := by
        simp only [Fin.val_succ]
        by_cases h : i.val % 2 = 1
        · have hh : (i.val + 1) % 2 ≠ 1 := by omega
          simp [h, hh]
        · have hh : (i.val + 1) % 2 = 1 := by omega
          simp [h, hh]
      rw [hpar]
      cases b <;> cases decide (i.val % 2 = 1) <;> rfl
    have heq :
        (fun i : Fin (k + 1) => Bool.xor b (decide (i.val % 2 = 1))) =
          Fin.cons b (fun i : Fin k => Bool.xor (!b) (decide (i.val % 2 = 1))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using htail j
    rw [heq, boolPacketPositiveCount_cons, ih]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true] <;> omega

/-- A constant raw facet packet has the central local index, in every arity
and for either value of its common raw orientation. -/
theorem localIndex_eq_central_of_constant_facets {n : ℕ} {V : Type*}
    (A : Hyper n V) (f : Fin (n + 1) ↪ V) (b : Bool)
    (hraw : ∀ i, A.orient (facet f i) = b) : localIndex A f = centralIndex n := by
  have hcount : positiveFacetCount A f =
      if b then n + 1 - (n + 1) / 2 else (n + 1) / 2 := by
    change boolPacketPositiveCount (fun i => normalizedFacet A f i) = _
    simpa only [normalizedFacet, hraw] using constantRawPacket_count (n + 1) b
  unfold localIndex centralIndex
  rw [hcount]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Constant canonical signs realize the central-only age at every finite
cardinality; the ambient order is used only to define the orientation. -/
theorem unboundedAdmissible_of_central (n : ℕ) (S : Set ℕ)
    (hcentral : centralIndex n ∈ S) : UnboundedAdmissible n S := by
  intro N
  refine ⟨N, le_rfl, Hyper.fromOrderedSigns (fun _ : Finset (Fin N) => false), ?_⟩
  apply (admissible_iff_canonical_all S _).mpr
  intro Q hQ
  have hraw (i : Fin (n + 1)) :=
    fromOrderedSigns_facet_increasing (fun _ : Finset (Fin N) => false)
      (Q.orderEmbOfFin hQ) i
  rw [localIndex_eq_central_of_constant_facets _ _ false hraw]
  exact hcentral

open StructuralRamsey
open StructuralRamsey.Structure

private def pureLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Empty
  relArity R := nomatch R
  funcArity F := nomatch F

private def pureModel (V : Type) : Structure pureLanguage V where
  rel R := nomatch R
  func F := nomatch F

private def orderedPureFin (k : ℕ) : Structure pureLanguage.withLinearOrder (Fin k) :=
  (pureModel (Fin k)).withLinearOrder

private theorem orderedPureFin_mem (k : ℕ) :
    CCO.UnaryHN.Native.AllOrderedModels pureLanguage (orderedPureFin k) := by
  refine ⟨pureModel (Fin k), inferInstance, ?_, rfl⟩
  intro F
  exact nomatch F

private def orderedPureFacet {n : ℕ} (i : Fin (n + 1)) :
    Embedding (orderedPureFin n) (orderedPureFin (n + 1)) where
  toFun := Fin.succAboveOrderEmb i
  injective := (Fin.succAboveOrderEmb i).injective
  map_rel_iff R t := by
    rcases R with R | _
    · exact nomatch R
    · exact (Fin.succAboveOrderEmb i).lt_iff_lt
  map_func F := nomatch F

/-- Unbounded admissible classes contain the central type. The only Ramsey
theorem used is finite Ramsey for structures in an empty language with a
free linear order, applied to the two actual finite orders of sizes n,n+1. -/
theorem central_of_unboundedAdmissible (n : ℕ) (S : Set ℕ)
    (hunbounded : UnboundedAdmissible n S) : centralIndex n ∈ S := by
  classical
  obtain ⟨V, hV, C, _hC, arrow⟩ :=
    CCO.UnaryHN.Native.allOrderedModels_ramsey pureLanguage
      (orderedPureFin n) (orderedPureFin (n + 1))
      (orderedPureFin_mem n) (orderedPureFin_mem (n + 1)) Bool
  let : Finite V := hV
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨m, hm, A, hA⟩ := hunbounded (Fintype.card V)
  let e : V ↪ Fin m := (Fintype.equivFin V).toEmbedding.trans
    (Fin.castLEOrderEmb hm).toEmbedding
  let colour : Embedding (orderedPureFin n) C → Bool :=
    fun t => A.orient (t.toFunctionEmbedding.trans e)
  obtain ⟨g, hg⟩ := arrow colour
  let f : Fin (n + 1) ↪ Fin m := g.toFunctionEmbedding.trans e
  have hraw (i : Fin (n + 1)) :
      A.orient (facet f i) = A.orient (facet f 0) := by
    exact hg (orderedPureFacet i) (orderedPureFacet 0)
  have hcentral := localIndex_eq_central_of_constant_facets A f _ hraw
  simpa only [hcentral] using hA f

/-- Central membership is exactly unbounded finite cardinality. This includes
empty finite carriers and requires neither validity nor an AP hypothesis. -/
theorem unboundedAdmissible_iff_central (n : ℕ) (S : Set ℕ) :
    UnboundedAdmissible n S ↔ centralIndex n ∈ S :=
  ⟨central_of_unboundedAdmissible n S, unboundedAdmissible_of_central n S⟩

end Hypertournaments
