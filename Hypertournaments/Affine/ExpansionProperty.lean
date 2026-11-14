import Hypertournaments.Affine.ExpansionCoding
import Hypertournaments.Affine.PairOrderHost
import Hypertournaments.Affine.PairOrdering
import Hypertournaments.Affine.PairRamsey
import Hypertournaments.Affine.HomogeneousGauge
import Hypertournaments.Affine.Potential
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# The expansion property for affine potential expansions

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". One fixed free oriented code survives
all later choices of target potential and order. A homogeneous lower gauge
is absorbed in a source pair supplied by the finite all-model host.
-/

universe u v w

namespace Hypertournaments.Affine

open StructuralRamsey
open StructuralRamsey.Structure

variable {Q : Type u} {G : Type v} [AddCommGroup G]

private abbrev Small (n : ℕ) := ULift.{w} (Fin n)

private def smallTuple (n : ℕ) : Fin n ↪ Small.{w} n :=
  ⟨ULift.up, ULift.up_injective⟩

private noncomputable def smallPair (n : ℕ) (d : Data Q G) :
    Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) (Small.{w} n) where
  low := Labelled.fromOrderedLabels (Palette.affine d.offset) (fun _ => 0)
  high := Labelled.fromOrderedLabels (Palette.free Q)
    (fun _ => (Classical.choose (d.onto 0), false))

private theorem no_small_tuple {n m : ℕ} (hnm : n < m) (t : Fin m ↪ Small.{w} n) : False := by
  have hc := Fintype.card_le_of_injective t t.injective
  simp only [Fintype.card_fin, Fintype.card_ulift] at hc
  omega

/-- On fewer than r vertices, both pair label structures have no tuples. -/
private noncomputable def smallEmbedding {n : ℕ} {d : Data Q G} {D : Type w} [LinearOrder D]
    (A : Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) D)
    (t : Fin n ↪o D) :
    Embedding (toOrderedPair (smallPair.{u,v,w} n d) inferInstance)
      (toOrderedPair A inferInstance) := by
  let eo : Small.{w} n ↪o D :=
    OrderEmbedding.ofStrictMono (fun x => t x.down) (fun _ _ h => t.strictMono h)
  exact pairOrderedEmbedding _ A eo
    ⟨fun s => (no_small_tuple (by omega) s).elim,
      fun s => (no_small_tuple (by omega) s).elim⟩

private theorem expansion_property_succ (n : ℕ) (hr : 2 ≤ n + 1)
    (d : Data Q G) [Finite Q] [Finite G]
    (ha : Even (n + 2) → d.offset = 0)
    {V : Type w} [Finite V] (rawA : Labelled (n + 2) d.palette V) :
    ∃ (W : Type w) (_ : Finite W) (rawB : Labelled (n + 2) d.palette W),
      Closed d rawB ∧
      ∀ (pA : Labelled (n + 1) (Palette.affine d.offset) V)
        (pB : Labelled (n + 1) (Palette.affine d.offset) W)
        (orderA : LinearOrder V) (orderB : LinearOrder W)
        (hpA : IsPotential d rawA pA) (hpB : IsPotential d rawB pB),
        Nonempty (Embedding (toOrderedExpansion (⟨rawA, pA, hpA⟩ : Expansion (n + 1) d V) orderA)
          (toOrderedExpansion (⟨rawB, pB, hpB⟩ : Expansion (n + 1) d W) orderB)) := by
  classical
  let : Nonempty Q := ⟨Classical.choose (d.onto 0)⟩
  let : Fintype G := Fintype.ofFinite G
  let anchor := smallPair.{u,v,w} n d
  obtain ⟨U, hU, D, orderD, hAll, hAnchor⟩ :=
    exists_all_pair_models_order_host_with (V := V) hr
      (Palette.affine d.offset) (Palette.free Q) anchor inferInstance
  let : Finite U := hU
  obtain ⟨X, hX, C, orderC, hRamsey⟩ :=
    exists_pair_ordered_ramsey_witness (n + 1) (Palette.affine d.offset) (Palette.free Q)
      anchor D inferInstance orderD G
  let : Finite X := hX
  obtain ⟨W, hW, target, hOrder⟩ :=
    pair_ordering_property hr (Palette.affine d.offset) (Palette.free Q) C
  let : Finite W := hW
  let base : Expansion (n + 1) d W := d.decodePair ha target
  have hEff : d.effectiveLabelled base.raw = target.low.coboundary ha := by
    apply Labelled.ext
    intro t
    exact d.decodeLabelled_effective (target.low.coboundary ha) target.high t
  have hCode : d.decodeLabelled (d.effectiveLabelled base.raw) target.high = base.raw := by
    rw [hEff]
    rfl
  refine ⟨W, hW, base.raw, base.compatible.closed, ?_⟩
  intro pA pB orderA orderB hpA hpB
  let : LinearOrder V := orderA
  let : LinearOrder U := orderD
  let : LinearOrder X := orderC
  let : LinearOrder W := orderB
  let EA : Expansion (n + 1) d V := ⟨rawA, pA, hpA⟩
  let EB : Expansion (n + 1) d W := ⟨base.raw, pB, hpB⟩
  obtain ⟨s, hs⟩ := exists_signed_gauge pB target.low
    (fun t => (hpB t).trans (base.compatible t).symm)
  obtain ⟨c⟩ := hOrder orderC orderB
  let χ : Embedding (toOrderedPair anchor inferInstance) (toOrderedPair C orderC) → G :=
    fun e => s.label ((smallTuple n).trans (c.comp e).toFunctionEmbedding)
  obtain ⟨g, hg⟩ := hRamsey χ
  let h := c.comp g
  obtain ⟨iAnchor⟩ := hAnchor
  let b : G := χ (g.comp iAnchor)
  have hhom : ∀ t : Fin n ↪o U, s.label (t.toEmbedding.trans h.toFunctionEmbedding) = b := by
    intro t
    exact hg (smallEmbedding D t) iAnchor
  have hPair := preserves_of_pairOrderedEmbedding D target orderD orderB h
  have hGauge : ∀ t : Fin (n + 1) ↪ U,
      pB.label (t.trans h.toFunctionEmbedding) =
        D.low.label t + signedCoboundary s.label (t.trans h.toFunctionEmbedding) := by
    intro t
    rw [hs, hPair.1 t]
  have hShift := preserves_after_homogeneous_gauge D.low pB s h.toFunctionEmbedding b hhom hGauge
  let drift : G := if Even (n + 1) then 0 else b
  let shifted : Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) V :=
    ⟨pA.affineAddLinear (constantLinear (n + 1) (-drift)), (EA.toCodePair orderA).high⟩
  obtain ⟨j⟩ := hAll shifted orderA
  have hJ := preserves_of_pairOrderedEmbedding shifted D orderA orderD j
  let e : V ↪ W := j.toFunctionEmbedding.trans h.toFunctionEmbedding
  have hPotential : pA.Preserves pB e := by
    apply Labelled.preserves_of_canonical
    intro S hS
    let t : Fin (n + 1) ↪o V := S.orderEmbOfFin hS
    change pB.label ((t.toEmbedding.trans j.toFunctionEmbedding).trans h.toFunctionEmbedding) = pA.label t.toEmbedding
    rw [hShift (t.toEmbedding.trans j.toFunctionEmbedding), Labelled.affineAddLinear_label,
      constantLinear_label_strictMono _ _ (j.strictMono.comp t.strictMono), hJ.1 t.toEmbedding]
    change pA.label t.toEmbedding + (constantLinear (n + 1) (-drift)).label t.toEmbedding + drift = _
    rw [constantLinear_label_strictMono _ _ t.strictMono]
    abel
  have hHigh : (EA.toCodePair orderA).high.Preserves target.high e := hJ.2.comp hPair.2
  let eo : V ↪o W := OrderEmbedding.ofStrictMono e (h.strictMono.comp j.strictMono)
  have hNative := pairOrderedEmbedding (EA.toCodePair orderA)
    (⟨pB, target.high⟩ : Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) W)
    eo ⟨hPotential, hHigh⟩
  have lifted := expansionEmbeddingOfCodeEmbedding ha EA orderA
    (⟨pB, target.high⟩ : Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) W) orderB hNative
  have hTarget : d.decodePair ha
      (⟨pB, target.high⟩ : Pair (n + 1) (Palette.affine d.offset) (Palette.free Q) W) = EB := by
    apply Expansion.ext
    · exact d.decode_fixed_code ha base.raw target.high hCode pB hpB
    · rfl
  rw [hTarget] at lifted
  exact ⟨lifted⟩

/-- Every finite closed affine-labelled structure has one fixed finite closed
host such that every potential-and-order expansion of the source embeds into
every potential-and-order expansion of that host. -/
theorem expansion_property (r : ℕ) (hr : 2 ≤ r) (d : Data Q G)
    [Finite Q] [Finite G] (ha : Even (r + 1) → d.offset = 0)
    {V : Type w} [Finite V] (rawA : Labelled (r + 1) d.palette V) (_hA : Closed d rawA) :
    ∃ (W : Type w) (_ : Finite W) (rawB : Labelled (r + 1) d.palette W),
      Closed d rawB ∧
      ∀ (pA : Labelled r (Palette.affine d.offset) V)
        (pB : Labelled r (Palette.affine d.offset) W)
        (orderA : LinearOrder V) (orderB : LinearOrder W)
        (hpA : IsPotential d rawA pA) (hpB : IsPotential d rawB pB),
        Nonempty (Embedding (toOrderedExpansion (⟨rawA, pA, hpA⟩ : Expansion r d V) orderA)
          (toOrderedExpansion (⟨rawB, pB, hpB⟩ : Expansion r d W) orderB)) := by
  cases r with
  | zero => omega
  | succ n => exact expansion_property_succ n hr d ha rawA

end Hypertournaments.Affine
