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

/-- The local orbit index, as the minority count of normalized facets. -/
def localIndex {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) : ℕ :=
  min ((Finset.univ.filter (fun i => normalizedFacet A f i = true)).card)
      ((Finset.univ.filter (fun i => normalizedFacet A f i = false)).card)

/-- Only local orbit indices in S may appear. -/
def Admissible {n : ℕ} {V : Type*} (S : Set ℕ) (A : Hyper n V) : Prop :=
  ∀ f : Fin (n + 1) ↪ V, localIndex A f ∈ S

example : centralIndex 4 = 2 := by decide
example : centralIndex 5 = 3 := by decide
example : 3 ∈ switchingAllowed 5 := by decide

end Hypertournaments
