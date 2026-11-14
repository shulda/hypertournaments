import Hypertournaments.Affine.PotentialBasics
import Hypertournaments.Affine.OrderedLabels
import Hypertournaments.Affine.SignedExactness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

/-!
# Existence of affine potentials and signed gauges

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Subtract one actual affine coboundary
to reduce to the ordinary signed simplex contraction. This leaves no
characteristic-two or two-divisibility assumption on the abelian group.
-/

universe u v w

namespace Hypertournaments.Affine

/-- Any auxiliary carrier order supplies one affine base cochain. Subtracting
its coboundary reduces a closed affine cochain to ordinary exactness. -/
theorem Labelled.exists_affine_potential_of_order {r : ℕ}
    {G : Type u} [AddCommGroup G] {a : G} {V : Type v} [LinearOrder V]
    (c : Labelled (r + 1) (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0)
    (hclosed : ∀ t : Fin (r + 2) ↪ V, signedCoboundary c.label t = 0) :
    ∃ p : Labelled r (Palette.affine a) V,
      ∀ t : Fin (r + 1) ↪ V, signedCoboundary p.label t = c.label t := by
  let base : Labelled r (Palette.affine a) V :=
    Labelled.fromOrderedLabels (Palette.affine a) (fun _ => 0)
  let upper := base.coboundary ha
  have hdiff : ∀ t : Fin (r + 2) ↪ V,
      signedCoboundary (c.affineSub upper).label t = 0 := by
    intro t
    change signedCoboundary (fun s => c.label s - upper.label s) t = 0
    rw [signedCoboundary_sub, hclosed t]
    change 0 - signedCoboundary (signedCoboundary base.label) t = 0
    rw [signedCoboundary_signedCoboundary_zero, sub_self]
  obtain ⟨linear, hlinear⟩ := exists_signed_potential (c.affineSub upper) hdiff
  refine ⟨base.affineAddLinear linear, ?_⟩
  intro t
  change signedCoboundary (fun s => base.label s + linear.label s) t = c.label t
  rw [signedCoboundary_add, hlinear t]
  change signedCoboundary base.label t + (c.label t - signedCoboundary base.label t) = _
  abel

/-- Every finite closed affine cochain has an affine potential. The carrier
order is chosen only inside the proof and is absent from the conclusion. -/
theorem Labelled.exists_affine_potential {r : ℕ}
    {G : Type u} [AddCommGroup G] {a : G} {V : Type v} [Finite V]
    (c : Labelled (r + 1) (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0)
    (hclosed : ∀ t : Fin (r + 2) ↪ V, signedCoboundary c.label t = 0) :
    ∃ p : Labelled r (Palette.affine a) V,
      ∀ t : Fin (r + 1) ↪ V, signedCoboundary p.label t = c.label t := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let : LinearOrder V := LinearOrder.lift' e e.injective
  exact c.exists_affine_potential_of_order ha hclosed

/-- Closedness of effective labels is precisely existence of a potential
for the actual raw structure, with arbitrary finite palette fibers. -/
theorem closed_iff_exists_potential {Q : Type u} {G : Type v} [AddCommGroup G]
    (d : Data Q G) {r : ℕ} {V : Type w} [Finite V]
    (ha : Even (r + 1) → d.offset = 0)
    (raw : Labelled (r + 1) d.palette V) :
    Closed d raw ↔ ∃ p : Labelled r (Palette.affine d.offset) V, IsPotential d raw p := by
  constructor
  · intro hclosed
    exact (d.effectiveLabelled raw).exists_affine_potential ha hclosed
  · rintro ⟨p, hp⟩
    exact hp.closed

/-- Two actual potentials differ by a signed lower alternating gauge. -/
theorem IsPotential.exists_gauge {Q : Type u} {G : Type v} [AddCommGroup G]
    {d : Data Q G} {r : ℕ} {V : Type w}
    {raw : Labelled (r + 2) d.palette V}
    {p q : Labelled (r + 1) (Palette.affine d.offset) V}
    (hp : IsPotential d raw p) (hq : IsPotential d raw q) :
    ∃ s : AlternatingCochain r V G,
      ∀ t : Fin (r + 1) ↪ V, p.label t = q.label t + signedCoboundary s.label t :=
  exists_signed_gauge p q (fun t => (hp t).trans (hq t).symm)

end Hypertournaments.Affine
