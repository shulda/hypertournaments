import Hypertournaments.OddToggleP3RandomSources

/-!
# Arbitrary source-bit prescriptions along the zero-sum transversal code

The exact potential-source index for every selected zero-sum transversal
and every deleted block was proved injective. Consequently EVERY
assignment of Boolean bits on these sources can be extended to an
assignment of the entire random-source family.

This is a deterministic surjectivity statement; together with the
finite-product counting identity, it supports later formalization of
independent uniform random bits. It does NOT by itself prove any
probability estimate or construct a nonamalgamation witness.
-/

namespace Hypertournaments

/-- Restriction of a full Boolean assignment to an injectively
indexed set of sources is always surjective. -/
theorem p3BoolRestriction_surjective
    {A B : Type*} (f : A → B) (hf : Function.Injective f) :
    Function.Surjective
      (fun values : B → Bool => fun a : A => values (f a)) := by
  intro target
  classical
  let values : B → Bool :=
    fun b => if h : ∃ a : A, f a = b
      then target (Classical.choose h)
      else false
  refine ⟨values, ?_⟩
  funext a
  have ha : ∃ x : A, f x = f a := ⟨a, rfl⟩
  change (if h : ∃ x : A, f x = f a
    then target (Classical.choose h)
    else false) = target a
  rw [dif_pos ha]
  have hchoose : Classical.choose ha = a :=
    hf (Classical.choose_spec ha)
  rw [hchoose]

/-- All prescribed Boolean values on punctured zero-sum transversals
are simultaneously realizable as evaluations of ONE global assignment
of the random potential bits. -/
theorem p3ZeroSumRandomSourceAssignments_surjective
    {G : Type*} [AddCommGroup G] (m : ℕ) :
    Function.Surjective
      (fun values :
          (Fin (m+1) × (Fin (m+1) → G)) → Bool =>
        fun fu :
            {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} × Fin (m+1) =>
          values (p3RandomSourceIndex m fu.1 fu.2)) := by
  exact p3BoolRestriction_surjective
    (fun fu :
      {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} × Fin (m+1) =>
      p3RandomSourceIndex m fu.1 fu.2)
    (p3RandomSourceIndex_injective m)

end Hypertournaments
