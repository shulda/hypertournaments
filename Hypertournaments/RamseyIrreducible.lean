import PartiteConstruction.Structure.FreeAmalgam

/-!
# Relation supports and native irreducibility

The Ramsey library uses universal no-crossing irreducibility. Pair coverage by
positive relation tuples implies this native predicate; no converse or
Gaifman replacement is used here. In a language without functions all subsets
are closed, so the support of any positive tuple is an induced irreducible.
-/

universe u v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Every subset is closed when there are no function symbols. -/
theorem closed_of_no_functions {L : Language.{u}} [IsEmpty L.FuncSymbol]
    {V : Type v} (C : Structure L V) (S : Set V) : C.IsClosed S := by
  intro F
  exact isEmptyElim F

/-- Positive relation tuples covering every pair force native irreducibility.
The ambient language may have functions: this direction needs no assumption
about them. -/
theorem irreducible_of_pair_coverage {L : Language.{u}} {V : Type v}
    (C : Structure L V)
    (h : ∀ x y : V, x ≠ y → ∃ (R : L.RelSymbol) (t : Fin (L.relArity R) → V),
      C.rel R t ∧ x ∈ Set.range t ∧ y ∈ Set.range t) : C.Irreducible := by
  classical
  intro H E F T Dsrc Esrc Fsrc Tsrc sE sF iE iF hfree e
  by_cases hleft : ∀ a : V, ∃ x : E, e a = iE x
  · exact Or.inl hleft
  right
  intro a
  by_contra hright
  obtain ⟨b, hb⟩ := not_forall.mp hleft
  have hba : b ≠ a := by
    intro heq
    subst b
    exact (hfree.covers (e a)).elim hb hright
  obtain ⟨R, t, ht, ⟨i, hi⟩, ⟨j, hj⟩⟩ := h b a hba
  have htarget : Tsrc.rel R (e ∘ t) := (e.map_rel_iff R t).mpr ht
  rcases (hfree.rel_iff R (e ∘ t)).mp htarget with
    ⟨xs, _, hxs⟩ | ⟨ys, _, hys⟩
  · apply hb
    refine ⟨xs i, ?_⟩
    simpa only [Function.comp_apply, hi] using congrFun hxs i
  · apply hright
    refine ⟨ys j, ?_⟩
    simpa only [Function.comp_apply, hj] using congrFun hys j

/-- The support of a positive relation tuple is an irreducible induced
substructure in a relational language, even when the tuple has repetitions. -/
theorem irreducible_relation_support {L : Language.{u}} [IsEmpty L.FuncSymbol]
    {V : Type v} (C : Structure L V) (R : L.RelSymbol)
    (t : Fin (L.relArity R) → V) (ht : C.rel R t) :
    (C.induce (Set.range t) (closed_of_no_functions C (Set.range t))).Irreducible := by
  apply irreducible_of_pair_coverage
  intro x y _
  let lifted : Fin (L.relArity R) → Set.range t := fun i => ⟨t i, ⟨i, rfl⟩⟩
  refine ⟨R, lifted, ht, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := x.property
    exact ⟨i, Subtype.ext hi⟩
  · obtain ⟨j, hj⟩ := y.property
    exact ⟨j, Subtype.ext hj⟩

end Hypertournaments.Ramsey
