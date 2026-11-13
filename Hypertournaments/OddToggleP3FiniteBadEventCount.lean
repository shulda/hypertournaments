import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Hypertournaments.OddToggleP3UniformSourceCounting

/-!
# Exact finite event counting for uniformly assigned potential bits

Let A ↪ B index selected independent Boolean source coordinates.
The global sample space is the set of all assignments B → Bool.
For any finite family P of prescribed patterns on the selected
coordinates, the event of global assignments whose restrictions lie
in P is a disjoint union of the exact restriction fibers.

The already certified uniform fiber equivalence makes every fiber
equipotent. Therefore the event count is exactly |P| times the
cardinality of any one restriction fiber. Combined with the
full-sample count this gives an integral counting identity
  2^|A| * |bad global assignments| = |P| * 2^|B|.
This is the FINITE analogue of the exact probability |P| / 2^|A|,
without introducing any measure or probability axioms.

The remaining p3 application needs to identify |P|=2 for each gauge
and to combine events across disjoint selected zero-sum transversals.
-/

namespace Hypertournaments

/-- Global assignments satisfying any one of the allowed selected
patterns are equivalent to the disjoint union of their fibers. -/
def p3BoolRestriction_badEventSigmaEquiv
    {A B : Type*} (f : A → B)
    (P : Finset (A → Bool)) :
    {v : B → Bool // (fun a : A => v (f a)) ∈ P} ≃
      (Σ p : {p : A → Bool // p ∈ P},
        {v : B → Bool // (fun a : A => v (f a)) = p.val}) where
  toFun v := ⟨⟨(fun a => v.1 (f a)), v.2⟩, ⟨v.1, rfl⟩⟩
  invFun z := ⟨z.2.1, by
    rw [z.2.2]
    exact z.1.2⟩
  left_inv := by
    intro v
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨p, hp⟩, ⟨v, hv⟩⟩
    cases hv
    rfl

/-- Every finite family P of selected patterns occupies precisely
|P| times one uniform fiber of the global Boolean assignment space. -/
theorem p3BoolRestriction_badEvent_card
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f)
    (P : Finset (A → Bool)) (target : A → Bool) :
    Nat.card
      {v : B → Bool // (fun a : A => v (f a)) ∈ P} =
      P.card * Nat.card
        {v : B → Bool // (fun a : A => v (f a)) = target} := by
  classical
  let PType := {p : A → Bool // p ∈ P}
  let Fiber (p : A → Bool) :=
    {v : B → Bool // (fun a : A => v (f a)) = p}
  have hEquiv :
      {v : B → Bool // (fun a : A => v (f a)) ∈ P} ≃
      (Σ p : PType, Fiber p.val) :=
    p3BoolRestriction_badEventSigmaEquiv f P
  have hsame (p : PType) :
      Fintype.card (Fiber p.val) = Nat.card (Fiber target) := by
    have hc := p3BoolRestriction_fibers_same_card f hf p.val target
    simpa only [Nat.card_eq_fintype_card] using hc
  calc
    Nat.card
        {v : B → Bool // (fun a : A => v (f a)) ∈ P} =
        Fintype.card
          {v : B → Bool // (fun a : A => v (f a)) ∈ P} := by
            simp only [Nat.card_eq_fintype_card]
    _ = Fintype.card (Σ p : PType, Fiber p.val) :=
      Fintype.card_congr hEquiv
    _ = ∑ p : PType, Fintype.card (Fiber p.val) := by simp
    _ = ∑ _p : PType, Nat.card (Fiber target) := by
      apply Finset.sum_congr rfl
      intro p _
      exact hsame p
    _ = P.card * Nat.card (Fiber target) := by
      simp [PType, Fintype.card_subtype]

/-- Exact finite frequency equation: selected patterns P occur
among all global Boolean assignments with relative frequency
|P|/2^|A|, stated without division or probability measures. -/
theorem p3BoolRestriction_badEvent_exact_ratio
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f)
    (P : Finset (A → Bool)) (target : A → Bool) :
    2 ^ (Fintype.card A) *
      Nat.card {v : B → Bool //
        (fun a : A => v (f a)) ∈ P} =
      P.card * 2 ^ (Fintype.card B) := by
  rw [p3BoolRestriction_badEvent_card f hf P target,
      p3BoolRestriction_exact_fiber_count f hf target]
  ring

end Hypertournaments
