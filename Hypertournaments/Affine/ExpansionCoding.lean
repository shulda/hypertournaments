import Hypertournaments.Affine.FiberCoding
import Hypertournaments.Affine.ExpansionLanguage
import Hypertournaments.Affine.SignedPermutation

/-!
# Intrinsic code pairs and actual affine potential expansions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Independent free oriented codes retain
all fibers of the raw palette, including fixed labels and duplicate codes.
The code remains fixed when a potential or a free vertex order changes.
-/

universe u v w z

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

variable {Q : Type u} {G : Type v} [AddCommGroup G]

/-- Decode independent potential and code structures into an actual expansion. -/
noncomputable def Data.decodePair (d : Data Q G) {r : ℕ}
    (ha : Even (r + 1) → d.offset = 0) {V : Type w}
    (A : Pair r (Palette.affine d.offset) (Palette.free Q) V) : Expansion r d V where
  raw := d.decodeLabelled (A.low.coboundary ha) A.high
  potential := A.low
  compatible t := (d.decodeLabelled_effective (A.low.coboundary ha) A.high t).symm

/-- A raw-preserving source code is chosen once from one source order. -/
noncomputable def Expansion.toCodePair {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) (order : LinearOrder V) :
    Pair r (Palette.affine d.offset) (Palette.free Q) V := by
  let : LinearOrder V := order
  exact ⟨A.potential, d.encode A.raw⟩

theorem Expansion.coboundary_eq_effective {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) (ha : Even (r + 1) → d.offset = 0) :
    A.potential.coboundary ha = d.effectiveLabelled A.raw := by
  apply Labelled.ext
  exact A.compatible

/-- Decoding the source code recovers the entire original actual expansion. -/
theorem Expansion.decode_toCodePair {r : ℕ} {d : Data Q G} {V : Type w}
    (A : Expansion r d V) (ha : Even (r + 1) → d.offset = 0) (order : LinearOrder V) :
    d.decodePair ha (A.toCodePair order) = A := by
  let : LinearOrder V := order
  apply Expansion.ext
  · change d.decodeLabelled (A.potential.coboundary ha) (d.encode A.raw) = A.raw
    rw [A.coboundary_eq_effective ha, d.decode_encode]
  · rfl

/-- Decoding preserves every actual injection preserving the independent
potential and code labels, without any vertex order hypothesis. -/
theorem Data.decodePair_preserves (d : Data Q G) {r : ℕ}
    (ha : Even (r + 1) → d.offset = 0) {V : Type w} {W : Type z}
    (A : Pair r (Palette.affine d.offset) (Palette.free Q) V)
    (B : Pair r (Palette.affine d.offset) (Palette.free Q) W)
    (e : V ↪ W) (he : A.Preserves B e) :
    (d.decodePair ha A).Preserves (d.decodePair ha B) e :=
  ⟨d.decodeLabelled_preserves e (he.1.coboundary ha) he.2, he.1⟩

/-- The same fixed code reconstructs the raw structure for every one of its
potentials. No auxiliary order occurs in the hypothesis or conclusion. -/
theorem Data.decode_fixed_code (d : Data Q G) {r : ℕ}
    (ha : Even (r + 1) → d.offset = 0) {V : Type w}
    (raw : Labelled (r + 1) d.palette V)
    (code : Labelled (r + 1) (Palette.free Q) V)
    (hcode : d.decodeLabelled (d.effectiveLabelled raw) code = raw)
    (p : Labelled r (Palette.affine d.offset) V) (hp : IsPotential d raw p) :
    (d.decodePair ha ⟨p, code⟩).raw = raw := by
  have h : p.coboundary ha = d.effectiveLabelled raw := Labelled.ext hp
  change d.decodeLabelled (p.coboundary ha) code = raw
  rw [h]
  exact hcode

/-- Forget the redundant raw label predicates and retain their fixed oriented
source codes; the actual native embedding function is unchanged. -/
noncomputable def codeEmbeddingOfExpansionEmbedding {r : ℕ} {d : Data Q G}
    {V : Type w} {W : Type z} (A : Expansion r d V) (B : Expansion r d W)
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (e : Embedding (toOrderedExpansion A orderA) (toOrderedExpansion B orderB)) :
    Embedding (toOrderedPair (A.toCodePair orderA) orderA)
      (toOrderedPair (B.toCodePair orderB) orderB) := by
  let : LinearOrder V := orderA
  let : LinearOrder W := orderB
  have hp := preserves_of_expansionOrderedEmbedding A B orderA orderB e
  let eo : V ↪o W := OrderEmbedding.ofStrictMono e e.strictMono
  exact pairOrderedEmbedding (A.toCodePair orderA) (B.toCodePair orderB) eo
    ⟨hp.2, d.encode_preserves A.raw B.raw eo hp.1⟩

/-- Lift an actual embedding into an arbitrary independent code-pair target.
Every raw label is reconstructed; the underlying function is unchanged. -/
noncomputable def expansionEmbeddingOfCodeEmbedding {r : ℕ} {d : Data Q G}
    (ha : Even (r + 1) → d.offset = 0) {V : Type w} {W : Type z}
    (A : Expansion r d V) (orderA : LinearOrder V)
    (C : Pair r (Palette.affine d.offset) (Palette.free Q) W) (orderC : LinearOrder W)
    (e : Embedding (toOrderedPair (A.toCodePair orderA) orderA) (toOrderedPair C orderC)) :
    Embedding (toOrderedExpansion A orderA) (toOrderedExpansion (d.decodePair ha C) orderC) := by
  let : LinearOrder V := orderA
  let : LinearOrder W := orderC
  have hp := preserves_of_pairOrderedEmbedding (A.toCodePair orderA) C orderA orderC e
  have hdecode := d.decodePair_preserves ha (A.toCodePair orderA) C e.toFunctionEmbedding hp
  rw [A.decode_toCodePair ha orderA] at hdecode
  let eo : V ↪o W := OrderEmbedding.ofStrictMono e e.strictMono
  exact expansionOrderedEmbedding A (d.decodePair ha C) eo hdecode

end Hypertournaments.Affine
