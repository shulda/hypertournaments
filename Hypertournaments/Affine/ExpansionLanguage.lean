import Hypertournaments.Affine.Data
import Hypertournaments.Affine.PairLanguage

/-!
# The native language of actual affine potential expansions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Every potential label and every raw label
is named, together with an independent free linear order. Membership requires
the actual coboundary equation on the entire carrier.
-/

universe u v w z

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

variable {Q : Type u} {G : Type v} [AddCommGroup G]

/-- The two named label structures underlying an actual potential expansion. -/
def Expansion.toPair {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) : Pair r (Palette.affine d.offset) d.palette V :=
  ⟨A.potential, A.raw⟩

abbrev expansionLanguage (r : ℕ) (d : Data Q G) :=
  pairLanguage r (Palette.affine d.offset) d.palette

abbrev orderedExpansionLanguage (r : ℕ) (d : Data Q G) :=
  orderedPairLanguage r (Palette.affine d.offset) d.palette

/-- All actual raw and potential labels are named, including relation reflection. -/
abbrev toExpansionNative {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) : Structure (expansionLanguage r d) V :=
  toPairNative A.toPair

/-- An actual affine potential expansion equipped with one free linear order. -/
abbrev toOrderedExpansion {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) (order : LinearOrder V) :
    Structure (orderedExpansionLanguage r d) V := toOrderedPair A.toPair order

/-- The original injection preserves both actual label structures. -/
def expansionNativeEmbedding {r : ℕ} {d : Data Q G} {V : Type w} {W : Type z}
    (A : Expansion r d V) (B : Expansion r d W) (e : V ↪ W)
    (he : A.Preserves B e) : Embedding (toExpansionNative A) (toExpansionNative B) :=
  pairNativeEmbedding A.toPair B.toPair e ⟨he.2, he.1⟩

theorem preserves_of_expansionNativeEmbedding {r : ℕ} {d : Data Q G}
    {V : Type w} {W : Type z} (A : Expansion r d V) (B : Expansion r d W)
    (e : Embedding (toExpansionNative A) (toExpansionNative B)) :
    A.Preserves B e.toFunctionEmbedding := by
  have h := preserves_of_pairNativeEmbedding A.toPair B.toPair e
  exact ⟨h.2, h.1⟩

/-- Native ordered embeddings preserve and reflect the potential, raw labels,
and the free order on all tuples. -/
def expansionOrderedEmbedding {r : ℕ} {d : Data Q G}
    {V : Type w} {W : Type z} [LinearOrder V] [LinearOrder W]
    (A : Expansion r d V) (B : Expansion r d W) (e : V ↪o W)
    (he : A.Preserves B e.toEmbedding) :
    Embedding (toOrderedExpansion A inferInstance) (toOrderedExpansion B inferInstance) :=
  pairOrderedEmbedding A.toPair B.toPair e ⟨he.2, he.1⟩

theorem preserves_of_expansionOrderedEmbedding {r : ℕ} {d : Data Q G}
    {V : Type w} {W : Type z} (A : Expansion r d V) (B : Expansion r d W)
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedExpansion A orderA) (toOrderedExpansion B orderB)) :
    A.Preserves B e.toFunctionEmbedding := by
  have h := preserves_of_pairOrderedEmbedding A.toPair B.toPair orderA orderB e
  exact ⟨h.2, h.1⟩

theorem strictMono_of_expansionOrderedEmbedding {r : ℕ} {d : Data Q G}
    {V : Type w} {W : Type z} [LinearOrder V] [LinearOrder W]
    (A : Expansion r d V) (B : Expansion r d W)
    (e : Embedding (toOrderedExpansion A inferInstance) (toOrderedExpansion B inferInstance)) :
    StrictMono e := e.strictMono

/-- Class membership includes an actual compatible expansion and a finite
entire carrier; the auxiliary order is free. -/
def orderedExpansionClass {r : ℕ} (d : Data Q G) {V : Type w}
    (C : Structure (orderedExpansionLanguage r d) V) : Prop :=
  Finite V ∧ ∃ (A : Expansion r d V) (order : LinearOrder V),
    C = toOrderedExpansion A order

end Hypertournaments.Affine
