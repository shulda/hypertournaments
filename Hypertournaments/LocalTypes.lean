import Hypertournaments.Basic

/-!
# Normalized local packets and the stable classification interface

The central type on n+1 vertices is indexed by floor((n+1)/2).
The parity family is the coboundary/switching alternative in odd arity.

We deliberately index types by natural numbers to keep statements stable
while proving their completeness as isomorphism invariants.
-/

namespace Hypertournaments

def centralIndex (n : ℕ) : ℕ := (n + 1) / 2

def nextCentralIndex (n : ℕ) : ℕ := centralIndex n - 1

/-- Indices allowed by the even/coboundary switching family. -/
def switchingAllowed (n : ℕ) : Set ℕ :=
  {d | d ≤ centralIndex n ∧ d % 2 = centralIndex n % 2}

/-- A set of real local type indices, excluding phantom indices above the central one. -/
def ValidTypes (n : ℕ) (S : Set ℕ) : Prop :=
  ∀ d ∈ S, d ≤ centralIndex n

/-- The intended final necessary condition, not yet a theorem about AP. -/
def NecessaryAlternatives (n : ℕ) (S : Set ℕ) : Prop :=
  nextCentralIndex n ∈ S ∨ (Odd n ∧ S = switchingAllowed n)

/-- Dropping coordinate i from a full (n+1)-tuple. -/
def facet {n : ℕ} {V : Type*} (f : Fin (n + 1) ↪ V)
    (i : Fin (n + 1)) : Fin n ↪ V :=
  (Fin.succAboveEmb i).trans f

/-- Normalize by the parity of the deleted coordinate. -/
def normalizedFacet {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) (i : Fin (n + 1)) : Bool :=
  Bool.xor (A.orient (facet f i)) (decide (i.val % 2 = 1))

/-- The number of positive normalized facets. This is the only
facet count needed computationally; the negative count is its complement. -/
def positiveFacetCount {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) : ℕ :=
  (Finset.univ.filter (fun i => normalizedFacet A f i = true)).card

/-- The local orbit index, as the minority count of normalized facets.
Using subtraction instead of a second filter makes the finite
computations and formal cardinality bounds simpler. -/
def localIndex {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) : ℕ :=
  min (positiveFacetCount A f) (n + 1 - positiveFacetCount A f)

/-- The positive facets form a subset of the n+1 available facets. -/
theorem positiveFacetCount_le {n : ℕ} {V : Type*}
    (A : Hyper n V) (f : Fin (n + 1) ↪ V) :
    positiveFacetCount A f ≤ n + 1 := by
  classical
  unfold positiveFacetCount
  simpa using
    (Finset.card_filter_le (Finset.univ : Finset (Fin (n + 1)))
      (fun i => normalizedFacet A f i = true))

/-- A local type index never exceeds the central index q. -/
theorem localIndex_le_central {n : ℕ} {V : Type*}
    (A : Hyper n V) (f : Fin (n + 1) ↪ V) :
    localIndex A f ≤ centralIndex n := by
  have h := positiveFacetCount_le A f
  unfold localIndex centralIndex
  omega

/-- Only local orbit indices in S may appear. -/
def Admissible {n : ℕ} {V : Type*} (S : Set ℕ) (A : Hyper n V) : Prop :=
  ∀ f : Fin (n + 1) ↪ V, localIndex A f ∈ S

/-- Enlarging the allowed local type set preserves admissibility. -/
theorem admissible_mono {n : ℕ} {V : Type*}
    {S T : Set ℕ} {A : Hyper n V}
    (hST : S ⊆ T) (hS : Admissible S A) :
    Admissible T A := by
  intro f
  exact hST (hS f)



/-- Restricting the allowed set to actual local indices does not
change the age of admissible hyperturnaments. -/
theorem admissible_validize {n : ℕ} {V : Type*}
    (S : Set ℕ) (A : Hyper n V) :
    Admissible S A ↔
      Admissible (S ∩ Set.Iic (centralIndex n)) A := by
  constructor
  · intro h f
    exact ⟨h f, localIndex_le_central A f⟩
  · intro h f
    exact (h f).1

/-- The switching family contains no non-existent indices. -/
theorem switchingAllowed_valid (n : ℕ) :
    ValidTypes n (switchingAllowed n) := by
  intro d hd
  exact hd.1

/-- The central index is always in the switching family. -/
theorem central_mem_switchingAllowed (n : ℕ) :
    centralIndex n ∈ switchingAllowed n := by
  exact ⟨le_refl _, rfl⟩

/-- Local index is natural with respect to vertex embeddings. -/
theorem localIndex_pullback {n : ℕ} {V : Type*} {W : Type*}
    (B : Hyper n W) (f : V ↪ W) (t : Fin (n + 1) ↪ V) :
    localIndex (B.pullback f) t = localIndex B (t.trans f) := by
  rfl

/-- Every induced sub-hypertournament of an admissible structure is admissible. -/
theorem admissible_pullback {n : ℕ} {V : Type*} {W : Type*}
    {S : Set ℕ} (B : Hyper n W) (f : V ↪ W)
    (h : Admissible S B) : Admissible S (B.pullback f) := by
  intro t
  rw [localIndex_pullback]
  exact h (t.trans f)

example : centralIndex 4 = 2 := by decide
example : centralIndex 5 = 3 := by decide
example : 3 ∈ switchingAllowed 5 := by
  change 3 ≤ centralIndex 5 ∧ 3 % 2 = centralIndex 5 % 2
  decide

end Hypertournaments
