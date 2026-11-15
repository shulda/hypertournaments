import Hypertournaments.EPPAExtension
import Mathlib.Tactic.Ext

/-!
# Restricting and reindexing the source of an ordinary EPPA witness

The actual subset partial isomorphisms are extended via the proved
between-copies interface; no coherent extension choice is introduced.
-/

universe u v w

namespace Hypertournaments

/-- A witness for a structure is also an unrestricted witness for each
induced substructure, along the original composite embedding. -/
theorem Hyper.IsEPPAWitness.pullback_source
    {n : ℕ} {U : Type u} {V : Type v} {W : Type w}
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W}
    (h : A.IsEPPAWitness B e) (f : U ↪ V) :
    (A.pullback f).IsEPPAWitness B (f.trans e) := by
  refine ⟨h.finite, ?_, ?_⟩
  · intro t
    exact h.preserves (t.trans f)
  · intro p
    let P := (A.pullback f).pullback (subsetEmbedding p.source)
    let i : p.source ↪ V := (subsetEmbedding p.source).trans f
    let j : p.source ↪ V := p.equiv.toEmbedding.trans ((subsetEmbedding p.target).trans f)
    have hi : Preserves P A i := by intro t; rfl
    have hj : Preserves P A j := by
      intro t
      exact p.preserves t
    obtain ⟨g, hg⟩ := h.extend_isomorphism P i j hi hj
    exact ⟨g, hg⟩

/-- The same witness extends partial automorphisms of any actually embedded
source structure, without first choosing an equality with a pullback. -/
theorem Hyper.IsEPPAWitness.of_preserves_source
    {n : ℕ} {U : Type u} {V : Type v} {W : Type w}
    {A : Hyper n V} {B : Hyper n W} {P : Hyper n U} {e : V ↪ W}
    (h : A.IsEPPAWitness B e) (f : U ↪ V) (hf : Preserves P A f) :
    P.IsEPPAWitness B (f.trans e) := by
  refine ⟨h.finite, h.preserves.comp hf, ?_⟩
  intro p
  let Q := P.pullback (subsetEmbedding p.source)
  let i : p.source ↪ V := (subsetEmbedding p.source).trans f
  let j : p.source ↪ V := p.equiv.toEmbedding.trans ((subsetEmbedding p.target).trans f)
  have hi : Preserves Q A i := by
    intro t
    exact hf (t.trans (subsetEmbedding p.source))
  have hj : Preserves Q A j := by
    intro t
    exact (hf ((t.trans p.equiv.toEmbedding).trans (subsetEmbedding p.target))).trans
      (p.preserves t)
  obtain ⟨g, hg⟩ := h.extend_isomorphism Q i j hi hj
  exact ⟨g, hg⟩

/-- The finite-ordinal class interface provides actual witnesses for every
finite source carrier and its original orientation-preserving injection. -/
theorem HasEPPA.exists_witness {n : ℕ} {family : ForbiddenFamily n}
    (hK : HasEPPA family) {V : Type u} [Finite V]
    (A : Hyper n V) (hA : Omits family A) :
    ∃ (b : ℕ) (B : Hyper n (Fin b)) (e : V ↪ Fin b),
      Omits family B ∧ A.IsEPPAWitness B e := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let s := Fintype.equivFin V
  let A' := A.pullback s.symm.toEmbedding
  obtain ⟨b, B, e, hB, hw⟩ := hK _ A' (omits_pullback hA s.symm.toEmbedding)
  have hsource : Preserves A A' s.toEmbedding := by
    intro t
    have ht : (t.trans s.toEmbedding).trans s.symm.toEmbedding = t := by
      ext i
      exact s.symm_apply_apply _
    change A.orient ((t.trans s.toEmbedding).trans s.symm.toEmbedding) = A.orient t
    rw [ht]
  exact ⟨b, B, s.toEmbedding.trans e, hB, hw.of_preserves_source s.toEmbedding hsource⟩

/-- Unrestricted finite-witness existence is hereditary under actual
orientation-preserving vertex embeddings. -/
theorem Hyper.HasFiniteEPPAWitness.of_preserves
    {n : ℕ} {U : Type u} {V : Type v} {P : Hyper n U} {A : Hyper n V}
    (h : A.HasFiniteEPPAWitness) (f : U ↪ V) (hf : Preserves P A f) :
    P.HasFiniteEPPAWitness := by
  obtain ⟨m, B, e, hw⟩ := h
  exact ⟨m, B, f.trans e, hw.of_preserves_source f hf⟩

end Hypertournaments
