import Lean.Elab.Tactic.Omega
import Hypertournaments.RamseyLanguage
import Hypertournaments.RamseyIrreducible
import Hypertournaments.PairCompletion
import CCO.UnaryHN.NativeTransferBasis
import Mathlib.Tactic.FinCases

/-!
# Extracting a consistent partial orientation from arbitrary relational inputs

The source is an arbitrary native R,< structure. The irreducible-piece
hypothesis, rather than the input type, supplies all orientation axioms.
Source: article pin 919349e7eceed3c7fa0ed126a337c6fae6624704,
`prop:link-completion` and the prescribed-domain argument.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

variable {n : ℕ} {V : Type v}

theorem map_pair {X Y : Type*} (e : X → Y) (x y : X) :
    e ∘ ![x, y] = ![e x, e y] := by
  funext i
  fin_cases i <;> rfl

/-- Rebase a model equality without transporting the underlying vertex map. -/
def modelEmbedding {X : Type v} (A : Hyper n X) (order : LinearOrder X)
    {E : Structure (orderedLanguage n) X} {C : Structure (orderedLanguage n) V}
    (hmodel : E = toOrderedNative A order) (e : Embedding E C) :
    Embedding (toOrderedNative A order) C where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    rw [← hmodel]
    exact e.map_rel_iff R t
  map_func F := nomatch F

def Compared (C : Structure (orderedLanguage n) V) (x y : V) : Prop :=
  C.rel (.inr ()) ![x, y] ∨ C.rel (.inr ()) ![y, x]

def ComparisonClique (C : Structure (orderedLanguage n) V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Compared C x y

/-- A clique of old comparisons is irreducible in the actual native sense. -/
theorem irreducible_comparison_clique
    (C : Structure (orderedLanguage n) V) (S : Set V) (hS : ComparisonClique C S) :
    (C.induce S (isClosed C S)).Irreducible := by
  apply irreducible_of_pair_coverage
  intro x y hxy
  have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  rcases hS x x.property y y.property hne with h | h
  · refine ⟨.inr (), ![x, y], ?_, ⟨(0 : Fin 2), rfl⟩, ⟨(1 : Fin 2), rfl⟩⟩
    change C.rel (.inr ()) (Subtype.val ∘ (![x, y] : Fin 2 → S))
    exact Eq.mpr (congrArg (C.rel (.inr ())) (map_pair Subtype.val x y)) h
  · refine ⟨.inr (), ![y, x], ?_, ⟨(1 : Fin 2), rfl⟩, ⟨(0 : Fin 2), rfl⟩⟩
    change C.rel (.inr ()) (Subtype.val ∘ (![y, x] : Fin 2 → S))
    exact Eq.mpr (congrArg (C.rel (.inr ())) (map_pair Subtype.val y x)) h

/-- A complete ordered source has a comparison clique as its image. -/
theorem comparisonClique_image {X : Type v}
    (A : Hyper n X) (order : LinearOrder X)
    (C : Structure (orderedLanguage n) V)
    (e : Embedding (toOrderedNative A order) C) :
    ComparisonClique C (Set.range e) := by
  intro x hx y hy hxy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  let : LinearOrder X := order
  have hab : a ≠ b := fun h => hxy (congrArg e h)
  rcases lt_or_gt_of_ne hab with h | h
  · left
    have hh := (e.map_rel_iff (.inr ()) ![a, b]).mpr h
    exact Eq.mp (congrArg (C.rel (.inr ())) (map_pair e a b)) hh
  · right
    have hh := (e.map_rel_iff (.inr ()) ![b, a]).mpr h
    exact Eq.mp (congrArg (C.rel (.inr ())) (map_pair e b a)) hh

noncomputable def rawSign (C : Structure (orderedLanguage n) V) (f : Fin n ↪ V) : Bool := by
  classical
  exact if C.rel (.inl ()) f then false else true

/-- Reflected relation truth reads the original Boolean orientation exactly. -/
theorem rawSign_of_embedding {X : Type v}
    (A : Hyper n X) (order : LinearOrder X)
    (C : Structure (orderedLanguage n) V)
    (e : Embedding (toOrderedNative A order) C) (f : Fin n ↪ X) :
    rawSign C (f.trans e.toFunctionEmbedding) = A.orient f := by
  classical
  have hrel : C.rel (.inl ()) (f.trans e.toFunctionEmbedding) ↔ A.orient f = false :=
    (e.map_rel_iff (.inl ()) f).trans (A.relation_embedding f)
  cases h : A.orient f <;> simp_all [rawSign]

/-- A relation tuple cannot have repetitions: its own support is irreducible. -/
theorem positive_relation_injective
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (t : Fin n → V) (ht : C.rel (.inl ()) t) : Function.Injective t := by
  let S := Set.range t
  let E := C.induce S (isClosed C S)
  have hE : E.Irreducible := irreducible_relation_support C (.inl ()) t ht
  obtain ⟨_, A, order, _, hmodel⟩ := hIrr E hE (C.inclusion S (isClosed C S))
  let lifted : Fin n → S := fun i => ⟨t i, ⟨i, rfl⟩⟩
  have hrel : E.rel (.inl ()) lifted := ht
  rw [hmodel] at hrel
  have hinj : Function.Injective lifted := hrel.1
  intro i j hij
  exact hinj (Subtype.ext hij)

theorem positive_relation_clique
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (t : Fin n → V) (ht : C.rel (.inl ()) t) : ComparisonClique C (Set.range t) := by
  let S := Set.range t
  let E := C.induce S (isClosed C S)
  have hE : E.Irreducible := irreducible_relation_support C (.inl ()) t ht
  obtain ⟨_, A, order, _, hmodel⟩ := hIrr E hE (C.inclusion S (isClosed C S))
  let e : Embedding (toOrderedNative A order) C := modelEmbedding A order hmodel (C.inclusion S (isClosed C S))
  have he := comparisonClique_image A order C e
  intro x hx y hy hxy
  exact he x ⟨⟨x, hx⟩, rfl⟩ y ⟨⟨y, hy⟩, rfl⟩ hxy

private theorem range_swap (f : Fin n ↪ V) (i j : Fin n) :
    Set.range ((Equiv.swap i j).toEmbedding.trans f) = Set.range f := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Equiv.swap i j k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Equiv.swap i j k, by simp⟩

private def intoRange (f : Fin n ↪ V) : Fin n ↪ Set.range f where
  toFun i := ⟨f i, ⟨i, rfl⟩⟩
  inj' _ _ h := f.injective (congrArg Subtype.val h)

/-- The alternating law is derived from an actual complete irreducible piece. -/
theorem rawSign_swap_of_clique
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (f : Fin n ↪ V) (hcl : ComparisonClique C (Set.range f))
    (i j : Fin n) (hij : i ≠ j) :
    rawSign C ((Equiv.swap i j).toEmbedding.trans f) = !(rawSign C f) := by
  let S := Set.range f
  let E := C.induce S (isClosed C S)
  have hE : E.Irreducible := irreducible_comparison_clique C S hcl
  obtain ⟨_, A, order, _, hmodel⟩ := hIrr E hE (C.inclusion S (isClosed C S))
  let e : Embedding (toOrderedNative A order) C := modelEmbedding A order hmodel (C.inclusion S (isClosed C S))
  have hf : (intoRange f).trans e.toFunctionEmbedding = f := by ext k; rfl
  have hswap : ((Equiv.swap i j).toEmbedding.trans (intoRange f)).trans
      e.toFunctionEmbedding = (Equiv.swap i j).toEmbedding.trans f := by ext k; rfl
  have h0 : rawSign C f = A.orient (intoRange f) :=
    (congrArg (rawSign C) hf.symm).trans (rawSign_of_embedding A order C e (intoRange f))
  have h1 : rawSign C ((Equiv.swap i j).toEmbedding.trans f) =
      A.orient ((Equiv.swap i j).toEmbedding.trans (intoRange f)) :=
    (congrArg (rawSign C) hswap.symm).trans
      (rawSign_of_embedding A order C e ((Equiv.swap i j).toEmbedding.trans (intoRange f)))
  exact h1.trans ((A.swap_flip (intoRange f) i j hij).trans (congrArg Bool.not h0.symm))

/-- Undefined tuples remain absent; comparison cliques inherit their forced sign. -/
noncomputable def partialOrientation
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C) :
    PartialHyper n V := by
  classical
  exact {
    orient f := if ComparisonClique C (Set.range f) then some (rawSign C f) else none
    swap_flip := by
      intro f i j hij
      simp only [range_swap]
      by_cases h : ComparisonClique C (Set.range f)
      · simp only [ite_eq_left h, Option.map_some]
        exact congrArg some (rawSign_swap_of_clique family C hIrr f h i j hij)
      · simp only [ite_eq_right h, Option.map_none]
  }

theorem partial_defined_iff
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (f : Fin n ↪ V) :
    (partialOrientation family C hIrr).orient f ≠ none ↔ ComparisonClique C (Set.range f) := by
  classical
  by_cases h : ComparisonClique C (Set.range f) <;> simp [partialOrientation, h]

noncomputable def missingPairs [Fintype V] (C : Structure (orderedLanguage n) V) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ¬ Compared C p.1 p.2)

theorem missingPairs_distinct [Fintype V]
    (C : Structure (orderedLanguage n) V) (p : V × V) (hp : p ∈ missingPairs C) : p.1 ≠ p.2 := by
  classical
  exact (Finset.mem_filter.mp hp).2.1

theorem partial_cliqueDomain [Fintype V]
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C) :
    (partialOrientation family C hIrr).HasCliqueDomain (missingPairs C) := by
  classical
  intro f
  rw [partial_defined_iff]
  constructor
  · intro h p hp ⟨h1, h2⟩
    exact (Finset.mem_filter.mp hp).2.2 (h p.1 h1 p.2 h2 (Finset.mem_filter.mp hp).2.1)
  · intro h x hx y hy hxy
    by_contra hcomp
    exact h (x, y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, hcomp⟩) ⟨hx, hy⟩

/-- A fully prescribed forbidden copy has an irreducible comparison-clique
support, so the original irreducible-piece membership excludes it. -/
theorem partial_omits
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C) :
    (partialOrientation family C hIrr).Omits family := by
  classical
  intro m F hF e hp
  have hn : 3 ≤ n := (hpc m F hF).1
  have hcl : ComparisonClique C (Set.range e) := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hne
    have hab : a ≠ b := fun h => hne (congrArg e h)
    obtain ⟨t, _, ht, _, _⟩ := (hpc m F hF).2.2 inferInstance a b hab
    have hdefined : (partialOrientation family C hIrr).orient (t.trans e) ≠ none := by
      rw [hp t]; simp
    have htuple := (partial_defined_iff family C hIrr (t.trans e)).mp hdefined
    exact htuple (e a) ⟨⟨0, by omega⟩, congrArg e (ht.1 ⟨0, by omega⟩ rfl)⟩
      (e b) ⟨⟨1, by omega⟩, congrArg e (ht.2.1 ⟨1, by omega⟩ rfl)⟩ hne
  let S := Set.range e
  let E := C.induce S (isClosed C S)
  have hE : E.Irreducible := irreducible_comparison_clique C S hcl
  obtain ⟨_, A, order, hA, hmodel⟩ := hIrr E hE (C.inclusion S (isClosed C S))
  let emb : Embedding (toOrderedNative A order) C := modelEmbedding A order hmodel (C.inclusion S (isClosed C S))
  let lifted : Fin m ↪ S := intoRange e
  apply hA m F hF lifted
  intro t
  have htuple : ComparisonClique C (Set.range (t.trans e)) := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
    exact hcl _ ⟨t i, rfl⟩ _ ⟨t j, rfl⟩ hne
  have horient := hp t
  simp only [partialOrientation, ite_eq_left htuple, Option.some.injEq] at horient
  have hcomp : (t.trans lifted).trans emb.toFunctionEmbedding = t.trans e := by ext k; rfl
  rw [← hcomp, rawSign_of_embedding A order C emb] at horient
  exact horient

end Hypertournaments.Ramsey
