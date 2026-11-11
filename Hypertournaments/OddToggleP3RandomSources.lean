import Hypertournaments.OddToggleP3ZeroSumCode

/-!
# Distinct random potential sources for zero-sum transversals

A selected zero-sum transversal has one independent potential variable
for each missing coordinate. The source is indexed by the missing block
and the retained coordinates. We encode this by a pair consisting of
the deleted index and the word with that coordinate replaced by zero.

The distance-two zero-sum code property makes the indexing map
injective: different selected transversals never reuse the same source
bit, even when different coordinates are deleted. This is the exact
finite combinatorial disjointness needed before applying independence
in the exceptional n ≡ 3 (mod 4) probability argument.

No probabilistic independence or existence of an amalgamation
obstruction is asserted in this module.
-/

namespace Hypertournaments

/-- Encode a punctured word by setting the deleted coordinate to zero.
The deleted coordinate itself is retained separately in the source index. -/
def p3PuncturedWord {G : Type*} [Zero G] (m : ℕ)
    (f : Fin (m+1) → G) (u : Fin (m+1)) : Fin (m+1) → G :=
  fun v => if v = u then 0 else f v

/-- The unique random-potential source associated with deleting coordinate u
of a selected zero-sum transversal. -/
def p3RandomSourceIndex {G : Type*} [AddCommGroup G] (m : ℕ)
    (f : {g : Fin (m+1) → G // (∑ i : Fin (m+1), g i) = 0})
    (u : Fin (m+1)) : Fin (m+1) × (Fin (m+1) → G) :=
  (u, p3PuncturedWord m f.1 u)

/-- Every deletion source has exactly one selected zero-sum transversal
and one missing coordinate. -/
theorem p3RandomSourceIndex_injective {G : Type*} [AddCommGroup G]
    (m : ℕ) :
    Function.Injective
      (fun fu :
        {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} × Fin (m+1) =>
        p3RandomSourceIndex m fu.1 fu.2) := by
  intro p q hpq
  rcases p with ⟨f, u⟩
  rcases q with ⟨g, v⟩
  change (u, p3PuncturedWord m f.1 u) =
    (v, p3PuncturedWord m g.1 v) at hpq
  have huv : u = v := congrArg Prod.fst hpq
  subst v
  have hpunct : p3PuncturedWord m f.1 u =
      p3PuncturedWord m g.1 u :=
    congrArg Prod.snd hpq
  have hfg : f.1 = g.1 :=
    p3ZeroSum_eq_of_agree_except m f.1 g.1 u f.2 g.2 (by
      intro i hi
      have hv := congrFun hpunct i
      simpa [p3PuncturedWord, hi] using hv)
  have heq : f = g := Subtype.ext hfg
  cases heq
  rfl

/-- The sets of potential sources used by two distinct zero-sum
transversals are disjoint. We state this as exact pairwise inequality
of all deleted-coordinate source indices. -/
theorem p3DistinctTransversals_disjoint_random_sources
    {G : Type*} [AddCommGroup G] (m : ℕ)
    (f g : {h : Fin (m+1) → G // (∑ i : Fin (m+1), h i) = 0})
    (hfg : f ≠ g)
    (u v : Fin (m+1)) :
    p3RandomSourceIndex m f u ≠ p3RandomSourceIndex m g v := by
  intro h
  have hpair := (p3RandomSourceIndex_injective m) (f, u) (g, v) h
  exact hfg (congrArg Prod.fst hpair)

end Hypertournaments
