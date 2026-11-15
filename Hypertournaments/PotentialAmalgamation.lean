import Hypertournaments.EvenPotential
import Hypertournaments.UnrestrictedAmalgamation
import Hypertournaments.OrderedStrongSpan

/-!
# Strong amalgamation of hypertournaments with chosen potentials

Compatible alternating potentials amalgamate on the same finite
exact-overlap carrier as unrestricted hypertournaments. Taking their
intrinsic coboundary then amalgamates the original orientations as well.
The construction also accommodates any compatible vertex orders.
-/

namespace Hypertournaments

universe u v w

/-- Strong amalgamation of the expanded structures consisting of an
orientation and a specified potential. No nonempty-base assumption is used. -/
theorem potential_strong_span {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (φA : Hyper r A) (φB : Hyper r B) (φC : Hyper r C)
    (BB : Hyper (r + 1) B) (CC : Hyper (r + 1) C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves φA φB f) (hAC : Preserves φA φC g)
    (hB : IsPotential BB φB) (hC : IsPotential CC φC) :
    ∃ (D : Hyper (r + 1) (FiniteStrongSpan.Carrier f g))
      (φD : Hyper r (FiniteStrongSpan.Carrier f g)),
      IsPotential D φD ∧
      Preserves φB φD (FiniteStrongSpan.left f g) ∧
      Preserves φC φD (FiniteStrongSpan.right f g) ∧
      Preserves BB D (FiniteStrongSpan.left f g) ∧
      Preserves CC D (FiniteStrongSpan.right f g) := by
  obtain ⟨φD, hBD, hCD⟩ := unrestricted_strong_span hr2 φA φB φC f g hAB hAC
  have hD := φD.coboundary_isPotential hr
  exact ⟨φD.coboundary hr, φD, hD, hBD, hCD,
    hB.preserves hD hBD, hC.preserves hD hCD⟩

/-- Compatible free linear orders can be preserved in the same expanded
strong amalgam, without changing its vertices or orientations. -/
theorem potential_ordered_strong_span {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {A : Type u} {B : Type v} {C : Type w}
    [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (φA : Hyper r A) (φB : Hyper r B) (φC : Hyper r C)
    (BB : Hyper (r + 1) B) (CC : Hyper (r + 1) C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : Preserves φA φB f.toEmbedding) (hAC : Preserves φA φC g.toEmbedding)
    (hB : IsPotential BB φB) (hC : IsPotential CC φC) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Hyper (r + 1) (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (φD : Hyper r (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      IsPotential D φD ∧
      Preserves φB φD (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves φC φD (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      Preserves BB D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves CC D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨order, hiOrder, hjOrder⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  obtain ⟨D, φD, hD, hi, hj, hBi, hCj⟩ := potential_strong_span hr hr2
    φA φB φC BB CC f.toEmbedding g.toEmbedding hAB hAC hB hC
  exact ⟨order, D, φD, hD, hi, hj, hBi, hCj, hiOrder, hjOrder⟩

end Hypertournaments
