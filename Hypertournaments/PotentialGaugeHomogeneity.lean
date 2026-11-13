import Hypertournaments.EvenPotentialGauge
import Hypertournaments.RamseyLanguage
import Mathlib.Data.ZMod.Basic

/-!
# Homogeneous scalar gauges disappear on an even potential arity

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:potential`. Each (r−1)-subset is the image of the unique ordered
small model. A common scalar colour need not be zero: its r equal
contributions cancel when r is even.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- The unique hypertournament on fewer vertices than its arity. -/
def smallGaugeModel (r : ℕ) : Hyper r (Fin (r - 1)) :=
  Hyper.fromOrderedSigns (fun _ => false)

def orderedSmallGaugeModel (r : ℕ) : Structure (orderedLanguage r) (Fin (r - 1)) :=
  toOrderedNative (smallGaugeModel r) inferInstance

/-- Every increasing (r−1)-tuple is an actual embedding of the small model. -/
def smallGaugeEmbedding {r : ℕ} (hr : 0 < r) {U : Type v}
    (D : Hyper r U) (orderD : LinearOrder U)
    (e : @OrderEmbedding (Fin (r - 1)) U inferInstance orderD.toLE) :
    Embedding (orderedSmallGaugeModel r) (toOrderedNative D orderD) := by
  apply @orderedEmbedding r (Fin (r - 1)) U inferInstance orderD (smallGaugeModel r) D e
  intro t
  have hle : r ≤ r - 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective t t.injective
  omega

/-- Every facet of an r-subset supplies a small-model embedding; hence
pairwise colour homogeneity suffices even without a separately chosen anchor. -/
theorem smallGauge_homogeneity_coboundary_zero {r : ℕ}
    (hr : Even r) (hrpos : 0 < r)
    {U : Type v} {S : Type w} [DecidableEq S]
    (D : Hyper r U) (orderD : LinearOrder U) (j : U ↪ S)
    (z : Finset S → ZMod 2)
    (hhom : ∀ e₁ e₂ : Embedding (orderedSmallGaugeModel r) (toOrderedNative D orderD),
      z (tupleVertices (e₁.toFunctionEmbedding.trans j)) =
        z (tupleVertices (e₂.toFunctionEmbedding.trans j)))
    (t : Fin r ↪ U) :
    Hypertournaments.coboundary z (tupleVertices (t.trans j)) = 0 := by
  classical
  let : LinearOrder U := orderD
  let F := tupleVertices t
  have hF : F.card = r := by
    dsimp [F, tupleVertices]
    rw [Finset.card_image_of_injective _ t.injective]
    simp
  have hne : F.Nonempty := Finset.card_pos.mp (hF ▸ hrpos)
  obtain ⟨a, ha⟩ := hne
  have hface (x : U) (hx : x ∈ F) : (F.erase x).card = r - 1 := by
    rw [Finset.card_erase_of_mem hx, hF]
  let e₀ := smallGaugeEmbedding hrpos D orderD ((F.erase a).orderEmbOfFin (hface a ha))
  let b := z (tupleVertices (e₀.toFunctionEmbedding.trans j))
  have hconst (x : U) (hx : x ∈ F) : z ((F.erase x).map j) = b := by
    let e := smallGaugeEmbedding hrpos D orderD ((F.erase x).orderEmbOfFin (hface x hx))
    have hh := hhom e e₀
    change z (tupleVertices (((F.erase x).orderEmbOfFin (hface x hx)).toEmbedding.trans j)) = b at hh
    have hv : tupleVertices ((F.erase x).orderEmbOfFin (hface x hx)).toEmbedding = F.erase x :=
      Finset.image_orderEmbOfFin_univ (F.erase x) (hface x hx)
    rw [tupleVertices_trans_map, hv] at hh
    exact hh
  rw [tupleVertices_trans_map]
  change Hypertournaments.coboundary z (F.map j) = 0
  unfold Hypertournaments.coboundary
  rw [Finset.sum_map]
  calc
    (∑ x ∈ F, z ((F.map j).erase (j x))) = ∑ x ∈ F, b := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.map_erase j F x]
      exact hconst x hx
    _ = r • b := by rw [Finset.sum_const, hF]
    _ = 0 := by
      obtain ⟨k, hk⟩ := hr
      rw [hk, add_nsmul]
      simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (k • b)

/-- Homogeneous gauge colours make the same actual ordered potential copy
preserve the switched potential on every injective tuple. -/
theorem gauge_homogeneity_preserves {r : ℕ} (hr : Even r) (hrpos : 0 < r)
    {U : Type v} {S : Type w} [DecidableEq S]
    (D : Hyper r U) (orderD : LinearOrder U)
    (φ₀ ψ : Hyper r S) (orderS : LinearOrder S)
    (h : Embedding (toOrderedNative D orderD) (toOrderedNative φ₀ orderS))
    (z : Finset S → ZMod 2)
    (hgauge : ∀ t : Fin r ↪ S, p1BitToZMod (ψ.orient t) =
      p1BitToZMod (φ₀.orient t) + Hypertournaments.coboundary z (tupleVertices t))
    (hhom : ∀ e₁ e₂ : Embedding (orderedSmallGaugeModel r) (toOrderedNative D orderD),
      z (tupleVertices (e₁.toFunctionEmbedding.trans h.toFunctionEmbedding)) =
        z (tupleVertices (e₂.toFunctionEmbedding.trans h.toFunctionEmbedding))) :
    Preserves D ψ h.toFunctionEmbedding := by
  intro t
  apply p1BitToZMod_injective
  rw [hgauge, smallGauge_homogeneity_coboundary_zero hr hrpos D orderD
    h.toFunctionEmbedding z hhom t, add_zero,
    preserves_of_orderedEmbedding D φ₀ orderD orderS h t]

end Hypertournaments.Ramsey
