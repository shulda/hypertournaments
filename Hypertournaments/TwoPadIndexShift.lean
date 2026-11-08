import Hypertournaments.TwoPadFacetGeometry
import Hypertournaments.TwoPadPacketCount
import Hypertournaments.TwoPadProfileEndpoint

/-!
# Exact local-type shift for intrinsic two-pad recovery

Three independent components now meet:

1. The recovered lower-arity hyperorientation is intrinsic (TwoPadSlice).
2. Deleting old coordinates of a padded tuple gives the corresponding
   padded old facets, including their normalized signs (TwoPadFacetGeometry).
3. The positive and minority counts of a Boolean packet increase by one
   when two opposite entries are prefixed (TwoPadPacketCount).

Equality of the two *raw* one-pad facets makes their normalized signs
opposite (TwoPadProfileEndpoint). The result is a full, uniform
local-index identity on actual hypertournament packets, not just an
abstract counting assertion.

The final reflection theorem still has to obtain the raw equality
via a pigeonhole profile for the mixed tuples of a one-point diagram.
-/

namespace Hypertournaments

/-- The ambient normalized packet of a padded old (n+1)-tuple is
exactly the two initial ambient signs followed by the normalized
packet of its recovered old slice. -/
theorem normalizedPacket_twoPadSlice_cons
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W) :
    (fun k : Fin (n + 3) =>
        normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) k) =
      Fin.cons
        (normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) 0)
        (Fin.cons
          (normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) 1)
          (fun i : Fin (n + 1) =>
            normalizedFacet (D.twoPadSlice g p q hp hq hpq) t i)) := by
  funext k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) k
  · rfl
  · rfl
  · simpa only [Fin.cons_succ] using
      (normalizedFacet_twoPadSlice_old D g p q hp hq hpq t i)

/-- An actual ambient local type increases by exactly one above
the old slice whenever its first two normalized signs are opposite. -/
theorem localIndex_twoPadSlice_shift_of_opposite
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W)
    (hopp : normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) 0 ≠
      normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) 1) :
    localIndex D (twoPadSliceTuple g p q hp hq hpq t) =
      localIndex (D.twoPadSlice g p q hp hq hpq) t + 1 := by
  let u : Fin (n + 3) → Bool :=
    fun k => normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t) k
  let v : Fin (n + 1) → Bool :=
    fun i => normalizedFacet (D.twoPadSlice g p q hp hq hpq) t i
  have hu : u = Fin.cons (u 0) (Fin.cons (u 1) v) := by
    exact normalizedPacket_twoPadSlice_cons D g p q hp hq hpq t
  have hnew :
      positiveFacetCount D (twoPadSliceTuple g p q hp hq hpq t) =
        boolPacketPositiveCount (Fin.cons (u 0) (Fin.cons (u 1) v)) := by
    change boolPacketPositiveCount u = _
    exact congrArg boolPacketPositiveCount hu
  have hold :
      positiveFacetCount (D.twoPadSlice g p q hp hq hpq) t =
        boolPacketPositiveCount v := rfl
  unfold localIndex
  rw [hnew, hold]
  exact boolPacketMinority_two_opposite (u 0) (u 1) v hopp

/-- Raw equality of the one-pad facets is the natural sufficient
hypothesis for the exact local-index shift. -/
theorem localIndex_twoPadSlice_shift_of_raw_equal
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W)
    (heq : D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 0) =
           D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 1)) :
    localIndex D (twoPadSliceTuple g p q hp hq hpq t) =
      localIndex (D.twoPadSlice g p q hp hq hpq) t + 1 := by
  exact localIndex_twoPadSlice_shift_of_opposite D g p q hp hq hpq t
    (normalized_first_two_opposite_of_raw_equal D _ heq)

/-- An actual ambient allowed type satisfying the profile equality
has its recovered lower index in the shifted allowed type set. -/
theorem twoPadSlice_localIndex_mem_shifted
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (T : Set ℕ)
    (hD : Admissible T D) (t : Fin (n + 1) ↪ W)
    (heq : D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 0) =
           D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 1)) :
    localIndex (D.twoPadSlice g p q hp hq hpq) t ∈ shiftedAllowed T := by
  change localIndex (D.twoPadSlice g p q hp hq hpq) t + 1 ∈ T
  have hallowed := hD (twoPadSliceTuple g p q hp hq hpq t)
  rw [localIndex_twoPadSlice_shift_of_raw_equal D g p q hp hq hpq t heq]
    at hallowed
  exact hallowed

/-- A useful uniform reflection interface: if all the relevant
one-pad raw facet pairs agree and the shifted allowed indices are
contained in the desired old class, the whole recovered slice is
admissible. For one-point amalgams one applies this to mixed tuples
and handles the other tuples through the source sides. -/
theorem Hyper.twoPadSlice_admissible_of_raw_equal
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (T S : Set ℕ)
    (hD : Admissible T D)
    (hshift : shiftedAllowed T ⊆ S)
    (hraw : ∀ t : Fin (n + 1) ↪ W,
      D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 0) =
      D.orient (facet (twoPadSliceTuple g p q hp hq hpq t) 1)) :
    Admissible S (D.twoPadSlice g p q hp hq hpq) := by
  intro t
  exact hshift (twoPadSlice_localIndex_mem_shifted D g p q hp hq hpq
    T hD t (hraw t))

end Hypertournaments
