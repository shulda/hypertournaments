import Hypertournaments.TwoPadIndexShift

/-!
# Mixed and nonmixed local admissibility in two-coordinate reflection

For a one-point amalgamation span, only old tuples containing both
new points require the pigeonhole/profile argument. Any old tuple
omitting at least one of the two new vertices is entirely contained
in one of the two original admissible sides.

We isolate this logical division from the combinatorial definition
of "mixed" and from the explicit one-point embedding geometry.
The mixed case is covered by the proven exact local-index shift;
the nonmixed case may be supplied from the side embeddings.

There is no unproved mathematical axiom: all further information
about the mixed predicate and original sides is kept as explicit
hypotheses.
-/

namespace Hypertournaments

/-- Local admissibility of the recovered two-pad slice follows by
partitioning old tuples into mixed and nonmixed. On the mixed part,
matching one-pad profiles force admissibility by the exact index
shift; on the nonmixed part, admissibility is inherited from source
side structures. -/
theorem Hyper.twoPadSlice_admissible_of_mixed_profile
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (T S : Set ℕ)
    (hD : Admissible T D)
    (hshift : shiftedAllowed T ⊆ S)
    (Mixed : (Fin (n + 1) ↪ W) → Prop)
    (hNonmixed : ∀ t : Fin (n + 1) ↪ W, ¬ Mixed t →
      localIndex (D.twoPadSlice g p q hp hq hpq) t ∈ S)
    (hMixed : ∀ t : Fin (n + 1) ↪ W, Mixed t →
      D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 0) =
      D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 1)) :
    Admissible S (D.twoPadSlice g p q hp hq hpq) := by
  intro t
  by_cases ht : Mixed t
  · exact hshift
      (twoPadSlice_localIndex_mem_shifted D g p q hp hq hpq T
        hD t (hMixed t ht))
  · exact hNonmixed t ht

/-- Recovery of the n-ary orientation on a source side implies
preservation of all its n-tuples by the embedding into the slice.
This statement uses the intrinsic ordinary-embedding predicate. -/
theorem Hyper.twoPadSlice_preserves_of_recovery
    {n : ℕ} {U W V : Type*}
    (A : Hyper n U) (D : Hyper (n + 2) V)
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (f : U ↪ W)
    (hrecover : ∀ t : Fin n ↪ U,
      D.orient (twoPadSliceTuple g p q hp hq hpq
        (t.trans f)) = A.orient t) :
    Preserves A (D.twoPadSlice g p q hp hq hpq) f := by
  intro t
  exact hrecover t

end Hypertournaments
