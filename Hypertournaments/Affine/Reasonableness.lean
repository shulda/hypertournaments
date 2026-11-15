import Hypertournaments.Affine.Potential
import Hypertournaments.Affine.GaugeAlignment
import Hypertournaments.OrderedStrongSpan

/-!
# Reasonableness of potential-and-order expansions

Source: `tex_hypertournaments` at
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`generalised_potential_structures_proof.tex`, the paragraph following `prop:sap`.
Every chosen potential and order extends along the prescribed raw embedding.
-/

namespace Hypertournaments.Affine

universe u v w z

/-- Extend a finite source order along an arbitrary injection. New points
may all be placed after the old points; the prescribed vertex map is retained. -/
theorem exists_linearOrder_extension {A : Type w} {C : Type z}
    [Finite A] [Finite C] [LinearOrder A] (e : A ↪ C) :
    ∃ order : LinearOrder C, @StrictMono A C inferInstance order.toPreorder e := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype C := Fintype.ofFinite C
  let rank (x : C) : ℕ :=
    if h : ∃ a, e a = x then OrderedStrongSpan.pointRank A (Classical.choose h)
    else Fintype.card A
  let key (x : C) : ℕ ×ₗ Fin (Fintype.card C) := toLex (rank x, Fintype.equivFin C x)
  have hinj : Function.Injective key := by
    intro x y h
    exact (Fintype.equivFin C).injective (congrArg (fun p => (ofLex p).2) h)
  let order : LinearOrder C := LinearOrder.lift' key hinj
  have hrank (a : A) : rank (e a) = OrderedStrongSpan.pointRank A a := by
    have h : ∃ b, e b = e a := ⟨a, rfl⟩
    dsimp only [rank]
    rw [dite_eq_left h]
    congr 1
    exact e.injective (Classical.choose_spec h)
  refine ⟨order, ?_⟩
  intro a b hab
  change key (e a) < key (e b)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  change rank (e a) < rank (e b)
  rw [hrank, hrank]
  exact OrderedStrongSpan.pointRank_strictMono A hab

/-- Any potential-and-order expansion of the source extends along the
original raw embedding into a fixed finite closed target reduct. -/
theorem expansion_reasonable {r : ℕ} (hr : 0 < r)
    {Q : Type u} {G : Type v} [AddCommGroup G] (d : Data Q G)
    (ha : Even (r + 1) → d.offset = 0)
    {A : Type w} {C : Type z} [Finite A] [Finite C]
    (AA : Expansion r d A) (rawC : Labelled (r + 1) d.palette C)
    (e : A ↪ C) (hAC : AA.raw.Preserves rawC e) (hC : Closed d rawC)
    (orderA : LinearOrder A) :
    ∃ (CC : Expansion r d C), CC.raw = rawC ∧
      ∃ orderC : LinearOrder C, AA.Preserves CC e ∧
        @StrictMono A C orderA.toPreorder orderC.toPreorder e := by
  obtain ⟨pC, hpC⟩ := (closed_iff_exists_potential d ha rawC).mp hC
  have hA : IsPotential d (rawC.pullback e) AA.potential := by
    intro t
    exact (AA.compatible t).trans (congrArg d.effective (hAC t).symm)
  obtain ⟨pC', hpC', he⟩ := hpC.exists_aligned AA.potential e hA hr
  let := orderA
  obtain ⟨orderC, horder⟩ := exists_linearOrder_extension e
  exact ⟨⟨rawC, pC', hpC'⟩, rfl, orderC, ⟨hAC, he⟩, horder⟩

end Hypertournaments.Affine
