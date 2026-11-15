import Hypertournaments.CanonicalOrientationRecovery
import Hypertournaments.FiniteClassAmalgamation
import CCO.UnaryHN.OrderedAmbient

/-!
# Constant-sign copies forced by finite Ramsey

The only Ramsey input is the previously proved native theorem for an empty
relational language with a free linear order. No Ramsey property of the
constrained hypertournament class is assumed. The carrier order is only an
auxiliary presentation of the constant-sign source.
-/

namespace Hypertournaments.FiveConstrained

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

private def orderedPureEmbedding {n k : ℕ} (e : Fin n ↪ Fin k)
    (he : StrictMono (e : Fin n → Fin k)) :
    Embedding (orderedPureFin n) (orderedPureFin k) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    rcases R with R | _
    · exact nomatch R
    · exact he.lt_iff_lt
  map_func F := nomatch F

/-- Every sufficiently large intrinsic hypertournament has a `k`-point copy
on which all increasing `n`-tuples have one common actual orientation bit. -/
theorem exists_constant_sign_copy (n k : ℕ) (hnk : n ≤ k) :
    ∃ N : ℕ, ∀ (m : ℕ), N ≤ m → ∀ A : Hyper n (Fin m),
      ∃ (e : Fin k ↪ Fin m) (b : Bool),
        ∀ t : Fin n ↪ Fin k, StrictMono (t : Fin n → Fin k) →
          A.orient (t.trans e) = b := by
  classical
  obtain ⟨V, hV, C, _hC, arrow⟩ :=
    CCO.UnaryHN.Native.allOrderedModels_ramsey pureLanguage
      (orderedPureFin n) (orderedPureFin k)
      (orderedPureFin_mem n) (orderedPureFin_mem k) Bool
  let : Finite V := hV
  let : Fintype V := Fintype.ofFinite V
  refine ⟨Fintype.card V, ?_⟩
  intro m hm A
  let eV : V ↪ Fin m := (Fintype.equivFin V).toEmbedding.trans
    (Fin.castLEOrderEmb hm).toEmbedding
  let colour : Embedding (orderedPureFin n) C → Bool :=
    fun t => A.orient (t.toFunctionEmbedding.trans eV)
  obtain ⟨g, hg⟩ := arrow colour
  let e : Fin k ↪ Fin m := g.toFunctionEmbedding.trans eV
  let t₀ : Fin n ↪o Fin k := Fin.castLEOrderEmb hnk
  refine ⟨e, A.orient (t₀.toEmbedding.trans e), ?_⟩
  intro t ht
  exact hg (orderedPureEmbedding t ht)
    (orderedPureEmbedding t₀.toEmbedding t₀.strictMono)

/-- The homogeneous copy is an actual embedding of a constant canonical-sign
hypertournament, with preservation on every ordered injective tuple. -/
theorem exists_preserving_constant (n k : ℕ) (hnk : n ≤ k) :
    ∃ N : ℕ, ∀ (m : ℕ), N ≤ m → ∀ A : Hyper n (Fin m),
      ∃ (e : Fin k ↪ Fin m) (b : Bool),
        Preserves (Hyper.fromOrderedSigns (fun _ : Finset (Fin k) => b)) A e := by
  obtain ⟨N, hN⟩ := exists_constant_sign_copy n k hnk
  refine ⟨N, ?_⟩
  intro m hm A
  obtain ⟨e, b, hb⟩ := hN m hm A
  refine ⟨e, b, ?_⟩
  have heq := orientations_equal_of_canonical
    (A.pullback e) (Hyper.fromOrderedSigns (fun _ : Finset (Fin k) => b))
  apply heq
  intro Q hQ
  let t : Fin n ↪o Fin k := Q.orderEmbOfFin hQ
  change A.orient (t.toEmbedding.trans e) =
    (Hyper.fromOrderedSigns (fun _ : Finset (Fin k) => b)).orient t.toEmbedding
  rw [fromOrderedSigns_orient_strictMono _ t.toEmbedding t.strictMono]
  exact hb t.toEmbedding t.strictMono

/-- An unbounded hereditary class must admit a constant-sign structure at
every fixed cardinality at least the arity. This includes the unavoidable
five-vertex ternary type used in the local classification. -/
theorem constant_member_of_unbounded {n : ℕ} {K : FiniteClass n}
    (hK : K.Hereditary) (hU : K.Unbounded) (k : ℕ) (hnk : n ≤ k) :
    ∃ b : Bool, K k (Hyper.fromOrderedSigns (fun _ : Finset (Fin k) => b)) := by
  obtain ⟨N, hN⟩ := exists_preserving_constant n k hnk
  obtain ⟨m, hm, A, hA⟩ := hU N
  obtain ⟨e, b, hp⟩ := hN m hm A
  exact ⟨b, hK _ A e hp hA⟩

end Hypertournaments.FiveConstrained
