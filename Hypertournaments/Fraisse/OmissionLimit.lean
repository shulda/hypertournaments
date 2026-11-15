import Hypertournaments.FirstOrderEncoding
import Hypertournaments.PairAmalgamation
import Hypertournaments.Fraisse.CountableAge
import Hypertournaments.Fraisse.Unbounded

/-!
# Countable homogeneous limits of pair-cancelling omission classes

The finite catalogue consists of all admitted intrinsic hypertournaments on
`Fin m`. Its actual amalgams feed the countable Fraïssé construction. The
result is decoded back to an intrinsic hypertournament, with exactly the
prescribed finite age.
-/

open FirstOrder
open FirstOrder.Language

set_option backward.isDefEq.respectTransparency false

namespace Hypertournaments.Fraisse.OmissionLimit

variable {n : ℕ}

/-- All admitted finite presentations, including isomorphic copies. -/
abbrev Chart (family : ForbiddenFamily n) :=
  Σ m : ℕ, {A : Hyper n (Fin m) // Omits family A}

instance (family : ForbiddenFamily n) : Countable (Chart family) := by
  infer_instance

private theorem small_omits (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {k : ℕ} (hk : k < n + 1) (A : Hyper n (Fin k)) : Omits family A := by
  intro m F hF e _
  have hlo : n + 1 ≤ m := by simpa using (hpc m F hF).2.1
  have hhi : m ≤ k := by simpa using Fintype.card_le_of_injective e e.injective
  omega

/-- The actual finite amalgamation data used by the construction. -/
noncomputable def data (hn : 3 ≤ n) (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    CountableAge.Data (Hyper.language n) where
  Chart := Chart family
  countableChart := inferInstance
  nonemptyChart := by
    let E := Hyper.fromOrderedSigns (n := n) (V := Fin 0) (fun _ => false)
    exact ⟨⟨0, E, small_omits family hpc (by omega) E⟩⟩
  Carrier i := Fin i.1
  finiteCarrier _ := inferInstance
  structureCarrier i := i.2.1.foStructure
  hereditary := by
    intro X instX hX i f
    let := instX
    let := hX
    let : Fintype X := Fintype.ofFinite X
    let := i.2.1.foStructure
    let e : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
    let B := i.2.1.pullback (e.toEmbedding.trans f.toEmbedding)
    have hB : Omits family B := omits_pullback i.2.2 _
    let := B.foStructure
    refine ⟨⟨Fintype.card X, B, hB⟩, ⟨{
      toEquiv := e.symm
      map_fun' := fun r => Empty.elim r
      map_rel' := ?_ }⟩⟩
    intro k r t
    cases r
    change B.Relation (e.symm ∘ t) ↔
      @FirstOrder.Language.Structure.RelMap _ X instX n Hyper.RelationSymbol.edge t
    rw [Hyper.relation_pullback]
    have ht : (e.toEmbedding.trans f.toEmbedding) ∘ (e.symm ∘ t) = f ∘ t := by
      funext x
      change f (e (e.symm (t x))) = f (t x)
      rw [e.apply_symm_apply]
    rw [ht]
    exact f.map_rel Hyper.RelationSymbol.edge t
  joint := by
    intro i j
    let := i.2.1.foStructure
    let := j.2.1.foStructure
    let e : Fin 0 ↪ Fin i.1 := Function.Embedding.ofIsEmpty
    let f : Fin 0 ↪ Fin j.1 := Function.Embedding.ofIsEmpty
    let E := i.2.1.pullback e
    have hE : Omits family E := omits_pullback i.2.2 e
    have he : Preserves E i.2.1 e := fun _ => rfl
    have hf : Preserves E j.2.1 f := by
      intro t
      exact Fin.elim0 (t ⟨0, by omega⟩)
    obtain ⟨d, D, a, b, hD, ha, hb, _, _⟩ :=
      pair_cancelling_hasStrongAmalgamation hn family hpc
        0 i.1 j.1 E i.2.1 j.2.1 hE i.2.2 j.2.2 e f he hf
    let := D.foStructure
    exact ⟨⟨d, D, hD⟩, ⟨Hyper.toFOEmbedding a ha⟩, ⟨Hyper.toFOEmbedding b hb⟩⟩
  amalgamate := by
    intro i j k f g
    let := i.2.1.foStructure
    let := j.2.1.foStructure
    let := k.2.1.foStructure
    obtain ⟨d, D, a, b, hD, ha, hb, hc, _⟩ :=
      pair_cancelling_hasStrongAmalgamation hn family hpc
        i.1 j.1 k.1 i.2.1 j.2.1 k.2.1 i.2.2 j.2.2 k.2.2
        f.toEmbedding g.toEmbedding
        (Hyper.preserves_of_foEmbedding f) (Hyper.preserves_of_foEmbedding g)
    let := D.foStructure
    refine ⟨⟨d, D, hD⟩, Hyper.toFOEmbedding a ha, Hyper.toFOEmbedding b hb, ?_⟩
    apply FirstOrder.Language.Embedding.ext
    intro x
    change a (f x) = b (g x)
    exact hc x

/-- The carrier of the internally constructed countable limit. -/
noncomputable abbrev Carrier (hn : 3 ≤ n) (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :=
  (data hn family hpc).Limit

noncomputable instance limitStructure (hn : 3 ≤ n) (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    (Hyper.language n).Structure (Carrier hn family hpc) := inferInstance

instance countable (hn : 3 ≤ n) (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    Countable (Carrier hn family hpc) := inferInstance

instance infinite (hn : 3 ≤ n) (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    Infinite (Carrier hn family hpc) := by
  apply (data hn family hpc).infinite_of_unbounded
  intro N
  obtain ⟨m, hm, A, hA⟩ := pair_cancelling_omission_unbounded hn family hpc N
  exact ⟨⟨m, A, hA⟩, ⟨Fin.castLEEmb hm⟩⟩

section Limit

variable (hn : 3 ≤ n) (family : ForbiddenFamily n)
  (hpc : ∀ m F, F ∈ family m → PairCancelling F)

private noncomputable def readOrientation (t : Fin n ↪ Carrier hn family hpc) : Bool := by
  classical
  exact if FirstOrder.Language.Structure.RelMap (L := Hyper.language n)
      Hyper.RelationSymbol.edge (t : Fin n → Carrier hn family hpc) then false else true

private theorem readOrientation_intoLimit (i : ℕ)
    (t : Fin n ↪ (data hn family hpc).Carrier ((data hn family hpc).stage i)) :
    readOrientation hn family hpc
      (t.trans ((data hn family hpc).intoLimit i).toEmbedding) =
      ((data hn family hpc).stage i).2.1.orient t := by
  classical
  unfold readOrientation
  let c : Chart family := (data hn family hpc).stage i
  let t' : Fin n ↪ Fin c.1 := t
  have h := ((data hn family hpc).intoLimit i).map_rel Hyper.RelationSymbol.edge
    (t : Fin n → (data hn family hpc).Carrier ((data hn family hpc).stage i))
  have hrel : FirstOrder.Language.Structure.RelMap (L := Hyper.language n)
      Hyper.RelationSymbol.edge (((data hn family hpc).intoLimit i) ∘ t) ↔
      c.2.1.Relation t' := h
  change (if FirstOrder.Language.Structure.RelMap (L := Hyper.language n) Hyper.RelationSymbol.edge
    (((data hn family hpc).intoLimit i) ∘ t) then false else true) = c.2.1.orient t'
  rw [hrel, Hyper.relation_embedding]
  cases c.2.1.orient t' <;> simp

private theorem tuple_in_stage {k : ℕ} (t : Fin k → Carrier hn family hpc) :
    ∃ (i : ℕ) (s : Fin k → (data hn family hpc).Carrier ((data hn family hpc).stage i)),
      ∀ x, (data hn family hpc).intoLimit i (s x) = t x := by
  obtain ⟨i, s, hs⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun i => (data hn family hpc).Carrier ((data hn family hpc).stage i))
    (data hn family hpc).chain t
  exact ⟨i, s, fun x => (congrFun hs x).symm⟩

private theorem embedding_in_stage (t : Fin n ↪ Carrier hn family hpc) :
    ∃ (i : ℕ) (s : Fin n ↪ (data hn family hpc).Carrier ((data hn family hpc).stage i)),
      s.trans ((data hn family hpc).intoLimit i).toEmbedding = t := by
  obtain ⟨i, s, hs⟩ := tuple_in_stage hn family hpc (t : Fin n → Carrier hn family hpc)
  have hi : Function.Injective s := by
    intro x y hxy
    apply t.injective
    rw [← hs x, ← hs y, hxy]
  refine ⟨i, ⟨s, hi⟩, ?_⟩
  ext x
  exact hs x

/-- The intrinsic hypertournament recovered from the actual limit relation. -/
noncomputable def hyper : Hyper n (Carrier hn family hpc) where
  orient := readOrientation hn family hpc
  swap_flip := by
    intro t a b hab
    obtain ⟨i, s, rfl⟩ := embedding_in_stage hn family hpc t
    change readOrientation hn family hpc
        (((Equiv.swap a b).toEmbedding.trans s).trans
          ((data hn family hpc).intoLimit i).toEmbedding) = _
    rw [readOrientation_intoLimit, readOrientation_intoLimit]
    exact ((data hn family hpc).stage i).2.1.swap_flip s a b hab

/-- The decoded orientation has exactly the native first-order relation,
including on tuples with repeated vertices. -/
theorem relation_iff (t : Fin n → Carrier hn family hpc) :
    FirstOrder.Language.Structure.RelMap (L := Hyper.language n) Hyper.RelationSymbol.edge t ↔
      (hyper hn family hpc).Relation t := by
  classical
  by_cases ht : Function.Injective t
  · change _ ↔ ∃ h : Function.Injective t,
      (hyper hn family hpc).orient ⟨t, h⟩ = false
    simp only [hyper, readOrientation]
    by_cases h : FirstOrder.Language.Structure.RelMap (L := Hyper.language n) Hyper.RelationSymbol.edge t <;>
      simp [h, ht]
  · have hnot : ¬ FirstOrder.Language.Structure.RelMap (L := Hyper.language n) Hyper.RelationSymbol.edge t := by
      obtain ⟨i, s, hs⟩ := tuple_in_stage hn family hpc t
      have he : ((data hn family hpc).intoLimit i) ∘ s = t := funext hs
      intro h
      rw [← he] at h
      have h' := (((data hn family hpc).intoLimit i).map_rel
        Hyper.RelationSymbol.edge s).mp h
      obtain ⟨hi, _⟩ := h'
      exact ht (by
        intro a b hab
        apply hi
        apply ((data hn family hpc).intoLimit i).injective
        rw [hs a, hs b]
        exact hab)
    exact iff_of_false hnot (Hyper.not_relation_of_not_injective _ t ht)

/-- A finite intrinsic embedding into the limit is a native first-order embedding. -/
noncomputable def toLimitEmbedding {m : ℕ} (A : Hyper n (Fin m))
    (e : Fin m ↪ Carrier hn family hpc) (he : Preserves A (hyper hn family hpc) e) :
    @FirstOrder.Language.Embedding (Hyper.language n) (Fin m) (Carrier hn family hpc)
      A.foStructure (limitStructure hn family hpc) := by
  let := A.foStructure
  exact {
    toEmbedding := e
    map_fun' := fun r => Empty.elim r
    map_rel' := by
      intro k r t
      cases r
      exact (relation_iff hn family hpc (e ∘ t)).trans
        ((preserves_iff_relation A (hyper hn family hpc) e).mp he t) }

/-- Native embeddings preserve the recovered intrinsic orientation. -/
theorem preserves_of_limitEmbedding {m : ℕ} (A : Hyper n (Fin m))
    (e : @FirstOrder.Language.Embedding (Hyper.language n) (Fin m) (Carrier hn family hpc)
      A.foStructure (limitStructure hn family hpc)) :
    Preserves A (hyper hn family hpc)
      (@FirstOrder.Language.Embedding.toEmbedding (Hyper.language n) (Fin m)
        (Carrier hn family hpc) A.foStructure (limitStructure hn family hpc) e) := by
  let := A.foStructure
  apply (preserves_iff_relation A (hyper hn family hpc) e.toEmbedding).mpr
  intro t
  exact (relation_iff hn family hpc (e ∘ t)).symm.trans
    (e.map_rel Hyper.RelationSymbol.edge t)

/-- Exact finite age: an actual finite structure embeds precisely when it
omits the selected forbidden family. -/
theorem finite_age (m : ℕ) (A : Hyper n (Fin m)) :
    (∃ e : Fin m ↪ Carrier hn family hpc, Preserves A (hyper hn family hpc) e) ↔
      Omits family A := by
  let := A.foStructure
  constructor
  · rintro ⟨e, he⟩
    have hAge := ((data hn family hpc).finite_age (Fin m)).mp
      ⟨toLimitEmbedding hn family hpc A e he⟩
    obtain ⟨i, ⟨f⟩⟩ := hAge
    exact omits_of_preserves (Hyper.preserves_of_foEmbedding f.toEmbedding) i.2.2
  · intro hA
    obtain ⟨e⟩ := (data hn family hpc).chart_embeds ⟨m, A, hA⟩
    change Fin m ↪[Hyper.language n] Carrier hn family hpc at e
    exact ⟨e.toEmbedding, preserves_of_limitEmbedding hn family hpc A e⟩

/-- Every finite intrinsic partial isomorphism extends to an intrinsic
automorphism of the constructed countable limit. -/
theorem homogeneous : (hyper hn family hpc).Homogeneous := by
  intro m A f g hf hg
  let := A.foStructure
  let F := toLimitEmbedding hn family hpc A f hf
  let G := toLimitEmbedding hn family hpc A g hg
  have hfg : FirstOrder.Language.Structure.FG (Hyper.language n) (Fin m) :=
    FirstOrder.Language.Structure.fg_iff_finite.mpr inferInstance
  obtain ⟨σ, hσ⟩ := (data hn family hpc).homogeneous F.toHom.range
    (hfg.range F.toHom) (G.comp F.equivRange.symm.toEmbedding)
  have hσpres : Preserves (hyper hn family hpc) (hyper hn family hpc)
      σ.toEquiv.toEmbedding := by
    apply (preserves_iff_relation _ _ _).mpr
    intro t
    exact (relation_iff hn family hpc (σ ∘ t)).symm.trans
      ((σ.map_rel Hyper.RelationSymbol.edge t).trans (relation_iff hn family hpc t))
  refine ⟨⟨σ.toEquiv, hσpres⟩, ?_⟩
  intro x
  have hx := congrArg (fun e : F.toHom.range ↪[Hyper.language n] Carrier hn family hpc =>
    e (F.equivRange x)) hσ
  change G (F.equivRange.symm (F.equivRange x)) = σ (F x) at hx
  rw [FirstOrder.Language.Equiv.symm_apply_apply] at hx
  exact hx.symm

end Limit

end Hypertournaments.Fraisse.OmissionLimit
