import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3ExplicitPotentials
import Hypertournaments.CanonicalPacket

/-!
# Missing any old block annihilates all-old p3 orientation facets

The common-base potential W is supported on full m-block transversals,
unlike side-link potentials L/R (which can omit one eligible block).
Hence a finite subset without the fresh vertex and lacking even one
old block has zero side-potential coboundary, for ANY W,L.

Consequently an actual increasing all-old (m+2)-packet missing a
block has all raw facet signs zero. This is the first, non-full-
transversal branch of the full p3 random side admissibility proof.
-/

namespace Hypertournaments

/-- A missing old block forces the full-transversal base potential
coefficient to vanish. -/
theorem p3BasePotential_zero_of_missing_block
    (m t : ℕ) (W : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) (i : Fin m)
    (hmissing : ∀ v ∈ U, p3BlockNumber t v ≠ i.val) :
    p3BasePotential m t W U = 0 := by
  classical
  have hzero : p3BlockOccupancy m t U i = 0 := by
    unfold p3BlockOccupancy
    have hfilter :
        U.filter (fun v => p3BlockNumber t v = i.val) = ∅ := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hv, heq⟩
        exact False.elim ((hmissing v hv) heq)
      · intro hv
        simp at hv
    rw [hfilter]
    rfl
  have hnot : ¬ p3IsBlockTransversal m t U := by
    intro h
    have hone := h.2 i
    rw [hzero] at hone
    omega
  simp [p3BasePotential, hnot]

/-- On an arbitrary all-old side subset missing one block,
the orientation coboundary is zero; eligible missing-block link
terms cannot appear because the fresh point is absent. -/
theorem p3SidePotential_coboundary_zero_old_missing_block
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V) (hfresh : fresh ∉ Q)
    (i : Fin m)
    (hmissing : ∀ v : Fin (m*t), old v ∈ Q →
       p3BlockNumber t v ≠ i.val) :
    coboundary (p3SidePotential m t old fresh eligible W L) Q = 0 := by
  classical
  unfold coboundary
  apply Finset.sum_eq_zero
  intro x hx
  have hnot : fresh ∉ Q.erase x := by
    intro hmem
    exact hfresh (Finset.mem_of_mem_erase hmem)
  rw [p3SidePotential_oldOnly m t old fresh eligible W L (Q.erase x) hnot]
  apply p3BasePotential_zero_of_missing_block m t W
    (p3SideOldPart old (Q.erase x)) i
  intro v hv
  have hvin : old v ∈ Q.erase x := by
    simpa [p3SideOldPart] using hv
  exact hmissing v (Finset.mem_of_mem_erase hvin)

/-- Every raw facet of an actual all-old increasing packet missing
one old block is zero, for arbitrary values of W and L. -/
theorem p3AllOldSidePacket_all_raw_facets_zero_of_missing_block
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin (m+2) ↪o V)
    (hfresh : fresh ∉ tupleVertices f.toEmbedding)
    (i : Fin m)
    (hmissing : ∀ v : Fin (m*t),
       old v ∈ tupleVertices f.toEmbedding →
         p3BlockNumber t v ≠ i.val) :
    ∀ q : Fin (m+2),
      (p3SideHyper m t old fresh eligible W L).orient
        (facet f.toEmbedding q) = false := by
  intro q
  have hverts := tupleVertices_facet_eq_erase f.toEmbedding q
  have hnot : fresh ∉ tupleVertices (facet f.toEmbedding q) := by
    rw [hverts]
    intro hv
    exact hfresh (Finset.mem_of_mem_erase hv)
  have hz : coboundary (p3SidePotential m t old fresh eligible W L)
      (tupleVertices (facet f.toEmbedding q)) = 0 := by
    apply p3SidePotential_coboundary_zero_old_missing_block
      m t old fresh eligible W L
      (tupleVertices (facet f.toEmbedding q)) hnot i
    intro v hv
    rw [hverts] at hv
    exact hmissing v (Finset.mem_of_mem_erase hv)
  change (Hyper.fromOrderedSigns
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q))).orient
    (facet f.toEmbedding q) = false
  rw [fromOrderedSigns_facet_increasing
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q)) f q]
  simp [hz, p3ZMod2ToBool]

end Hypertournaments
