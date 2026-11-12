import Hypertournaments.OddToggleP3RandomSources
import Hypertournaments.OddToggleP3ZeroSumCount

/-!
# Combined W, L and R random sources for complete p3 trials

On a selected zero-sum transversal q of length s+1, the p3
obstruction reads one potential bit for each of its s+1
deleted-coordinate link facets, plus the independent full
transversal base bit W(q). This is exactly s+2 Boolean bits.

Link source indices are given by the certified injective
p3RandomSourceIndex s q i. The base bit lives in a DISJOINT
summand from all link bits and is indexed by the full q.

Thus the combined indexing
 (q, Sum.inl i) -> Sum.inl (link source at deleted i)
 (q, Sum.inr ()) -> Sum.inr (full base source q)
is injective across ALL selected zero-sum transversals and
within each trial. No random variables can be accidentally
reused, including between W and L/R.

The selected index set has exactly (s+2)*|G|^s coordinates.
This is the genuine finite combinatorial independent-source
input for exact per-trial probability 2^(-(s+1)).
No age/AP/probability conclusion is asserted in this module.
-/

namespace Hypertournaments

/-- Each selected trial has s+1 independent link-source indices
and one separate full-transversal base-source index. -/
def p3FullTrialSourceIndex
    {G : Type*} [AddCommGroup G] (s : ℕ)
    (qi : {q : Fin (s+1) → G //
      (∑ i : Fin (s+1), q i) = 0} × (Fin (s+1) ⊕ Unit)) :
    (Fin (s+1) × (Fin (s+1) → G)) ⊕ (Fin (s+1) → G) :=
  match qi.2 with
  | Sum.inl i => Sum.inl (p3RandomSourceIndex s qi.1 i)
  | Sum.inr _ => Sum.inr qi.1.1

/-- No two distinct selected (zero-sum transversal, position)
pairs consume the same W/L/R potential source bit. -/
theorem p3FullTrialSourceIndex_injective
    {G : Type*} [AddCommGroup G] (s : ℕ) :
    Function.Injective (p3FullTrialSourceIndex (G:=G) s) := by
  intro x y h
  rcases x with ⟨qx, ix⟩
  rcases y with ⟨qy, iy⟩
  cases ix with
  | inl i =>
    cases iy with
    | inl j =>
      change Sum.inl (p3RandomSourceIndex s qx i) =
        Sum.inl (p3RandomSourceIndex s qy j) at h
      have hh : (qx, i) = (qy, j) :=
        (p3RandomSourceIndex_injective s) (Sum.inl.inj h)
      cases hh
      rfl
    | inr u =>
      change Sum.inl (p3RandomSourceIndex s qx i) =
        Sum.inr qy.1 at h
      cases h
  | inr u =>
    cases iy with
    | inl j =>
      change Sum.inr qx.1 =
        Sum.inl (p3RandomSourceIndex s qy j) at h
      cases h
    | inr v =>
      change Sum.inr qx.1 = Sum.inr qy.1 at h
      have hq : qx = qy :=
        Subtype.ext (Sum.inr.inj h)
      cases hq
      cases u
      cases v
      rfl

/-- Exactly s+2 independent bits are sampled for each of the
|G|^s selected zero-sum transversals, counting the W bit as well
as all s+1 link bits. -/
theorem p3FullTrialSourceIndex_card
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) :
    Fintype.card
      ({q : Fin (s+1) → G //
        (∑ i : Fin (s+1), q i) = 0} × (Fin (s+1) ⊕ Unit)) =
      (s+2) * (Fintype.card G)^s := by
  classical
  rw [Fintype.card_prod, p3ZeroSumTuple_card]
  simp [Fintype.card_sum, mul_comm]

end Hypertournaments
