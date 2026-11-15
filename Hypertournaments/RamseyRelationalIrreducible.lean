import Hypertournaments.RamseyIrreducible

/-!
# Native irreducibility equals relational pair coverage

In a language without functions, a missing pair gives a free decomposition
into the two induced complements of its endpoints. Thus the native universal
no-crossing predicate is exactly the article's relational irreducibility,
without a finiteness assumption or a strengthened completion hypothesis.
-/

universe u v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- The article's relational irreducibility: every distinct pair occurs in
one positive relation tuple. -/
def PairCovered {L : Language.{u}} {V : Type v} (C : Structure L V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ (R : L.RelSymbol) (t : Fin (L.relArity R) → V),
    C.rel R t ∧ x ∈ Set.range t ∧ y ∈ Set.range t

/-- Without functions, native irreducibility forces relational pair coverage. -/
theorem pair_coverage_of_irreducible {L : Language.{u}} [IsEmpty L.FuncSymbol]
    {V : Type v} (C : Structure L V) (hC : C.Irreducible) : PairCovered C := by
  classical
  intro x y hxy
  by_contra hpair
  let LS : Set V := {z | z ≠ x}
  let RS : Set V := {z | z ≠ y}
  let MS : Set V := LS ∩ RS
  let AL := C.induce LS (closed_of_no_functions C LS)
  let AR := C.induce RS (closed_of_no_functions C RS)
  let AM := C.induce MS (closed_of_no_functions C MS)
  let ml : Embedding AM AL := {
    toFun := fun z => ⟨z.val, z.property.1⟩
    injective := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : LS => z.val) hab)
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := fun F => isEmptyElim F }
  let mr : Embedding AM AR := {
    toFun := fun z => ⟨z.val, z.property.2⟩
    injective := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : RS => z.val) hab)
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := fun F => isEmptyElim F }
  let il := C.inclusion LS (closed_of_no_functions C LS)
  let ir := C.inclusion RS (closed_of_no_functions C RS)
  have hfree : IsFreeAmalgam ml mr il ir := by
    constructor
    · intro z
      by_cases hz : z = x
      · exact Or.inr ⟨⟨z, by change z ≠ y; simpa [hz] using hxy⟩, rfl⟩
      · exact Or.inl ⟨⟨z, hz⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have he : a.val = b.val := hab
        refine ⟨⟨a.val, a.property, ?_⟩, rfl, ?_⟩
        · simpa only [he] using b.property
        · exact Subtype.ext he.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R t
      constructor
      · intro ht
        by_cases hx : x ∈ Set.range t
        · have hy : ∀ i, t i ≠ y := by
            intro i hi
            exact hpair ⟨R, t, ht, hx, ⟨i, hi⟩⟩
          exact Or.inr ⟨(fun i => ⟨t i, hy i⟩), ht, rfl⟩
        · have hh : ∀ i, t i ≠ x := by
            intro i hi
            exact hx ⟨i, hi⟩
          exact Or.inl ⟨(fun i => ⟨t i, hh i⟩), ht, rfl⟩
      · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) <;> exact hs
    · intro F
      exact isEmptyElim F
  rcases hC hfree (Embedding.id C) with hl | hr
  · obtain ⟨z, hz⟩ := hl x
    exact z.property hz.symm
  · obtain ⟨z, hz⟩ := hr y
    exact z.property hz.symm

/-- Exact equivalence of the library and article irreducibility predicates. -/
theorem irreducible_iff_pair_coverage {L : Language.{u}} [IsEmpty L.FuncSymbol]
    {V : Type v} (C : Structure L V) : C.Irreducible ↔ PairCovered C :=
  ⟨pair_coverage_of_irreducible C, irreducible_of_pair_coverage C⟩

end Hypertournaments.Ramsey
