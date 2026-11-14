import Hypertournaments.Affine.LabelledAmalgamation
import Hypertournaments.Affine.ExpansionCoding
import Hypertournaments.Affine.Potential
import Hypertournaments.Affine.GaugeAlignment
import Lean.Elab.Tactic.Omega

/-!
# Strong amalgamation for affine potential expansions and their closed reducts

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. Independent potential and fiber-code
amalgams decode on the original exact-overlap carrier. A signed gauge
aligns potentials for closed reducts before applying expanded amalgamation.
-/

universe u v w z s

namespace Hypertournaments.Affine

variable {Q : Type u} {G : Type v} [AddCommGroup G]

/-- Actual potential expansions strongly amalgamate along arbitrary intrinsic
embeddings. No order restriction or finiteness of the palette is imposed. -/
theorem expanded_strong_span {r : ℕ} (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {A : Type w} {B : Type z} {C : Type s} [Finite B] [Finite C]
    (AA : Expansion r d A) (BB : Expansion r d B) (CC : Expansion r d C)
    (f : A ↪ B) (g : A ↪ C) (hAB : AA.Preserves BB f) (hAC : AA.Preserves CC g) :
    ∃ D : Expansion r d (FiniteStrongSpan.Carrier f g),
      BB.Preserves D (FiniteStrongSpan.left f g) ∧
      CC.Preserves D (FiniteStrongSpan.right f g) := by
  classical
  let : Nonempty Q := ⟨Classical.choose (d.onto 0)⟩
  let X := FiniteStrongSpan.Carrier f g
  let i := FiniteStrongSpan.left f g
  let j := FiniteStrongSpan.right f g
  let : Fintype X := Fintype.ofFinite X
  let orderX : LinearOrder X := LinearOrder.lift' (Fintype.equivFin X)
    (Fintype.equivFin X).injective
  let : LinearOrder X := orderX
  let orderB : LinearOrder B := LinearOrder.lift' i i.injective
  let orderC : LinearOrder C := LinearOrder.lift' j j.injective
  let orderA : LinearOrder A := LinearOrder.lift' (f.trans i) (f.trans i).injective
  let : LinearOrder A := orderA
  let : LinearOrder B := orderB
  let : LinearOrder C := orderC
  have hf : StrictMono f := by intro x y h; exact h
  have hg : StrictMono g := by
    intro x y h
    change @LT.lt X orderX.toLT (j (g x)) (j (g y))
    rw [← FiniteStrongSpan.commutes f g x, ← FiniteStrongSpan.commutes f g y]
    exact h
  let fo : A ↪o B := OrderEmbedding.ofStrictMono f hf
  let go : A ↪o C := OrderEmbedding.ofStrictMono g hg
  have hcodeB : (d.encode AA.raw).Preserves (d.encode BB.raw) f :=
    d.encode_preserves AA.raw BB.raw fo hAB.1
  have hcodeC : (d.encode AA.raw).Preserves (d.encode CC.raw) g :=
    d.encode_preserves AA.raw CC.raw go hAC.1
  obtain ⟨p, hpB, hpC⟩ := labelled_strong_span AA.potential BB.potential CC.potential f g hAB.2 hAC.2
  obtain ⟨code, hcB, hcC⟩ := labelled_strong_span (d.encode AA.raw) (d.encode BB.raw)
    (d.encode CC.raw) f g hcodeB hcodeC
  let pair : Pair r (Palette.affine d.offset) (Palette.free Q) X := ⟨p, code⟩
  refine ⟨d.decodePair ha pair, ?_, ?_⟩
  · have h := d.decodePair_preserves ha (BB.toCodePair orderB) pair i ⟨hpB, hcB⟩
    rw [BB.decode_toCodePair ha orderB] at h
    exact h
  · have h := d.decodePair_preserves ha (CC.toCodePair orderC) pair j ⟨hpC, hcC⟩
    rw [CC.decode_toCodePair ha orderC] at h
    exact h

/-- Closed affine-labelled structures strongly amalgamate after aligning
actual side potentials by a signed lower gauge on the common base. -/
theorem closed_strong_span {r : ℕ} (hr : 2 ≤ r) (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {A : Type w} {B : Type z} {C : Type s} [Finite B] [Finite C]
    (AA : Labelled (r + 1) d.palette A) (BB : Labelled (r + 1) d.palette B)
    (CC : Labelled (r + 1) d.palette C)
    (f : A ↪ B) (g : A ↪ C) (hAB : AA.Preserves BB f) (hAC : AA.Preserves CC g)
    (hB : Closed d BB) (hC : Closed d CC) :
    ∃ D : Labelled (r + 1) d.palette (FiniteStrongSpan.Carrier f g),
      Closed d D ∧ BB.Preserves D (FiniteStrongSpan.left f g) ∧
        CC.Preserves D (FiniteStrongSpan.right f g) := by
  obtain ⟨pB, hpB⟩ := (closed_iff_exists_potential d ha BB).mp hB
  obtain ⟨pC, hpC⟩ := (closed_iff_exists_potential d ha CC).mp hC
  let pA := pB.pullback f
  have hpA : IsPotential d AA pA := by
    intro t
    exact (hpB (t.trans f)).trans (congrArg d.effective (hAB t))
  have hpAC : IsPotential d (CC.pullback g) pA := by
    intro t
    exact (hpA t).trans (congrArg d.effective (hAC t).symm)
  obtain ⟨pC', hpC', hAC'⟩ := hpC.exists_aligned pA g hpAC (by omega)
  let EA : Expansion r d A := ⟨AA, pA, hpA⟩
  let EB : Expansion r d B := ⟨BB, pB, hpB⟩
  let EC : Expansion r d C := ⟨CC, pC', hpC'⟩
  have hEAB : EA.Preserves EB f := ⟨hAB, fun _ => rfl⟩
  have hEAC : EA.Preserves EC g := ⟨hAC, hAC'⟩
  obtain ⟨D, hi, hj⟩ := expanded_strong_span d ha EA EB EC f g hEAB hEAC
  exact ⟨D.raw, D.compatible.closed, hi.1, hj.1⟩

end Hypertournaments.Affine
