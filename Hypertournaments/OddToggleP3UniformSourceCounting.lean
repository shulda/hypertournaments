import Hypertournaments.OddToggleP3UniformSourceFibers

/-!
# Exact finite uniform-product cardinality of random source restrictions

The global Boolean assignment space decomposes canonically as a
dependent sum of fibers of its restriction to selected coordinates:
  (B → Bool) ≃ Σ p : A → Bool, {v : B → Bool // v ∘ f = p}.

The fiber-equivalence theorem for injective f makes every summand
equipotent. Counting the total Boolean functions yields the exact
finite identity
  2^|B| = 2^|A| * |fiber(p)|.

In the uniform distribution on global bit assignments, each
selected bit pattern therefore has probability 2^(-|A|). This
module only establishes the NATURAL-NUMBER cardinality identity,
not an analytic probability measure or the AP obstruction.
-/

namespace Hypertournaments

/-- Every global bit assignment is uniquely a selected bit word
together with a global extension of precisely that word. -/
def p3BoolRestriction_totalSigmaEquiv
    {A B : Type*} (f : A → B) :
    (B → Bool) ≃
      (Σ p : A → Bool,
        {values : B → Bool // (fun a : A => values (f a)) = p}) where
  toFun v := ⟨(fun a => v (f a)), ⟨v, rfl⟩⟩
  invFun v := v.2.1
  left_inv _ := rfl
  right_inv := by
    intro v
    rcases v with ⟨p, ⟨values, hvalues⟩⟩
    cases hvalues
    rfl

/-- Finite uniform bit assignments on B restrict to a prescribed
pattern on the injective source indices A with exactly the
cardinality dictated by the product-counting identity. -/
theorem p3BoolRestriction_exact_fiber_count
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f)
    (target : A → Bool) :
    2 ^ (Fintype.card B) =
      2 ^ (Fintype.card A) *
        Fintype.card
          {values : B → Bool // (fun a : A => values (f a)) = target} := by
  classical
  calc
    2 ^ (Fintype.card B) =
        Fintype.card (B → Bool) := by simp
    _ = Fintype.card
        (Σ p : A → Bool,
          {values : B → Bool // (fun a : A => values (f a)) = p}) :=
      Fintype.card_congr (p3BoolRestriction_totalSigmaEquiv f)
    _ = ∑ p : A → Bool,
        Fintype.card
          {values : B → Bool // (fun a : A => values (f a)) = p} := by
            simp
    _ = ∑ _p : A → Bool,
        Fintype.card
          {values : B → Bool // (fun a : A => values (f a)) = target} := by
            apply Finset.sum_congr rfl
            intro p _
            exact p3BoolRestriction_fibers_same_card f hf p target
    _ = 2 ^ (Fintype.card A) *
        Fintype.card
          {values : B → Bool // (fun a : A => values (f a)) = target} := by
            simp

end Hypertournaments
