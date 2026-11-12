import Hypertournaments.OddToggleP3SourceAssignments
import Hypertournaments.OddToggleP3BoolPhases

/-!
# Uniform fibers of finite random-source Boolean assignments

For any injection f : A → B, the restriction from all Boolean
assignments B → Bool to assignments on A has uniform fibers.
Given two target words p,q on A, use surjectivity of restriction
to extend the XOR phase p ^^ q to a shift word on B. Translation
by that word is an involutive equivalence between the two fibers.

In particular all fibers have the SAME finite cardinality. This is
the precise equiprobability statement needed before developing
the finite Bernoulli-product counting for selected p3 zero-sum
transversal sources. It does not assert any specific probability
formula or amalgamation obstruction.
-/

namespace Hypertournaments

/-- Boolean assignments on all sources restricting to two
different prescribed bit patterns have canonically equivalent
fibers, by an XOR translation extending their difference. -/
noncomputable def p3BoolRestriction_fiberEquiv
    {A B : Type*} (f : A → B) (hf : Function.Injective f)
    (p q : A → Bool) :
    {values : B → Bool // (fun a : A => values (f a)) = p} ≃
      {values : B → Bool // (fun a : A => values (f a)) = q} := by
  classical
  let hsurj :=
    p3BoolRestriction_surjective f hf (fun a : A => p a ^^ q a)
  let shift : B → Bool := Classical.choose hsurj
  have hshift :
      (fun a : A => shift (f a)) = (fun a : A => p a ^^ q a) :=
    Classical.choose_spec hsurj
  have hs (a : A) : shift (f a) = p a ^^ q a :=
    congrFun hshift a
  have hforward (v : {values : B → Bool //
        (fun a : A => values (f a)) = p}) :
      (fun a : A => (p3BoolTranslate shift v.1) (f a)) = q := by
    funext a
    have hv : v.1 (f a) = p a := congrFun v.2 a
    change v.1 (f a) ^^ shift (f a) = q a
    rw [hv, hs a]
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq]
  have hreverse (v : {values : B → Bool //
        (fun a : A => values (f a)) = q}) :
      (fun a : A => (p3BoolTranslate shift v.1) (f a)) = p := by
    funext a
    have hv : v.1 (f a) = q a := congrFun v.2 a
    change v.1 (f a) ^^ shift (f a) = p a
    rw [hv, hs a]
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq]
  refine
    { toFun := fun v => ⟨p3BoolTranslate shift v.1, hforward v⟩
      invFun := fun v => ⟨p3BoolTranslate shift v.1, hreverse v⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    apply Subtype.ext
    exact p3BoolTranslate_involutive shift v.1
  · intro v
    apply Subtype.ext
    exact p3BoolTranslate_involutive shift v.1

/-- Every prescribed assignment on an injectively indexed set of
finite sources has the same number of global Boolean extensions. -/
theorem p3BoolRestriction_fibers_same_card
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f)
    (p q : A → Bool) :
    Nat.card
      {values : B → Bool // (fun a : A => values (f a)) = p} =
    Nat.card
      {values : B → Bool // (fun a : A => values (f a)) = q} := by
  classical
  exact Nat.card_congr (p3BoolRestriction_fiberEquiv f hf p q)

end Hypertournaments
