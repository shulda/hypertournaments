import Hypertournaments.EvenPotential
import Hypertournaments.RamseyLanguage

/-!
# The actual language of potential expansions

There are two orientation relations, in arities r and r+1, and a free
linear order. The potential equation makes preservation of the higher
relation automatic, but the relation remains present in every embedding.
Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`, `thm:potential`.
-/

universe v w

namespace Hypertournaments

namespace Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Both the potential and its coboundary are named relations. -/
def potentialLanguage (r : ℕ) : Language where
  RelSymbol := Bool
  FuncSymbol := Empty
  relArity b := if b then r + 1 else r
  funcArity F := nomatch F

abbrev orderedPotentialLanguage (r : ℕ) := (potentialLanguage r).withLinearOrder

def toPotentialNative {r : ℕ} {V : Type v}
    (A : Hyper (r + 1) V) (φ : Hyper r V) : Structure (potentialLanguage r) V where
  rel | false, t => φ.Relation t | true, t => A.Relation t
  func F := nomatch F

/-- The freely ordered expansion retaining both intrinsic orientations. -/
def toOrderedPotential {r : ℕ} {V : Type v}
    (A : Hyper (r + 1) V) (φ : Hyper r V) (order : LinearOrder V) :
    Structure (orderedPotentialLanguage r) V :=
  @Structure.withLinearOrder (potentialLanguage r) V (toPotentialNative A φ) order.toLT

/-- Every potential embedding lifts to an embedding of the full expansion. -/
def liftPotentialEmbedding {r : ℕ} {V : Type v} {W : Type w}
    {A : Hyper (r + 1) V} {B : Hyper (r + 1) W}
    {φ : Hyper r V} {ψ : Hyper r W}
    (hA : IsPotential A φ) (hB : IsPotential B ψ)
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedNative φ orderA) (toOrderedNative ψ orderB)) :
    Embedding (toOrderedPotential A φ orderA) (toOrderedPotential B ψ orderB) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    rcases R with b | u
    · cases b with
      | false => exact e.map_rel_iff (.inl ()) t
      | true =>
        exact (preserves_iff_relation A B e.toFunctionEmbedding).mp
          (hA.preserves hB
            (preserves_of_orderedEmbedding φ ψ orderA orderB e)) t
    · exact e.map_rel_iff (.inr ()) t
  map_func F := nomatch F

/-- Forgetting the named coboundary leaves the same ordered potential map. -/
def forgetPotentialEmbedding {r : ℕ} {V : Type v} {W : Type w}
    {A : Hyper (r + 1) V} {B : Hyper (r + 1) W}
    {φ : Hyper r V} {ψ : Hyper r W}
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedPotential A φ orderA) (toOrderedPotential B ψ orderB)) :
    Embedding (toOrderedNative φ orderA) (toOrderedNative ψ orderB) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    rcases R with u | u
    · exact e.map_rel_iff (.inl false) t
    · exact e.map_rel_iff (.inr ()) t
  map_func F := nomatch F

end Ramsey
end Hypertournaments
