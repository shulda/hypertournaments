import Hypertournaments.Independent.ClassBridge
import Hypertournaments.PairOrdering
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# Transfer of the independently stated link theorem

The statement module is unchanged. The native Ramsey and ordering witnesses
are transported along genuine embeddings, with their arbitrary finite carriers
relabeled by Fin. In particular the target in the ordering property is chosen
before either of its subsequently quantified orders.
-/

universe u v w

namespace IndependentHypertournaments

namespace Bridge

noncomputable section

/-- The native relational encoding of an independently defined ordered object. -/
def nativeOrdered {n : ℕ} {V : Type u} (A : OrderedHypertournament n V) :=
  Hypertournaments.Ramsey.toOrderedNative (toHyper A.reduct) (toLinearOrder A.order)

/-- Independent ordered embeddings give full native relational embeddings. -/
def orderedNativeEmbedding {n : ℕ} {V : Type u} {W : Type v}
    (A : OrderedHypertournament n V) (B : OrderedHypertournament n W)
    (f : V → W) (hf : OrderedEmbeds A B f) :
    StructuralRamsey.Structure.Embedding (nativeOrdered A) (nativeOrdered B) := by
  let e : V ↪ W := ⟨f, hf.1.1⟩
  refine {
    toFun := f
    injective := hf.1.1
    map_rel_iff := ?_
    map_func := ?_ }
  · intro R t
    cases R with
    | inl R =>
      exact (Hypertournaments.preserves_iff_relation (toHyper A.reduct)
        (toHyper B.reduct) e).mp
          ((embeds_iff_preserves A.reduct B.reduct e).mp hf.1) t
    | inr R =>
      change Fin 2 → V at t
      change @LT.lt W (toLinearOrder B.order).toLT (f (t 0)) (f (t 1)) ↔
        @LT.lt V (toLinearOrder A.order).toLT (t 0) (t 1)
      simpa only [toLinearOrder_lt] using (hf.2 (t 0) (t 1)).symm
  · intro F
    exact nomatch F

/-- A full native embedding recovers the independent ordered embedding. -/
theorem orderedEmbeds_of_native {n : ℕ} {V : Type u} {W : Type v}
    (A : OrderedHypertournament n V) (B : OrderedHypertournament n W)
    (e : StructuralRamsey.Structure.Embedding (nativeOrdered A) (nativeOrdered B)) :
    OrderedEmbeds A B e := by
  refine ⟨(embeds_iff_preserves A.reduct B.reduct e.toFunctionEmbedding).mpr
    (Hypertournaments.Ramsey.preserves_of_orderedEmbedding
      (toHyper A.reduct) (toHyper B.reduct) (toLinearOrder A.order)
      (toLinearOrder B.order) e), ?_⟩
  intro a b
  have h := e.map_rel_iff (.inr ()) ![a, b]
  change @LT.lt W (toLinearOrder B.order).toLT (e a) (e b) ↔
    @LT.lt V (toLinearOrder A.order).toLT a b at h
  exact (toLinearOrder_lt A.order a b).symm.trans
    (h.symm.trans (toLinearOrder_lt B.order (e a) (e b)))

/-- Transport an arbitrary native ordered object to an equivalent carrier. -/
def reindexOrdered {n : ℕ} {X : Type u} {Y : Type v}
    (D : Hypertournaments.Hyper n X) (order : LinearOrder X) (s : Y ≃ X) :
    OrderedHypertournament n Y where
  reduct := ofHyper (D.pullback s.toEmbedding)
  order := ofLinearOrder (@LinearOrder.lift' Y X order s s.injective)

/-- The independent embedding produced by relabeling a native target. -/
theorem orderedEmbeds_of_native_reindex {n : ℕ}
    {V : Type u} {X : Type v} {Y : Type w}
    (A : OrderedHypertournament n V) (D : Hypertournaments.Hyper n X)
    (order : LinearOrder X) (s : Y ≃ X)
    (e : StructuralRamsey.Structure.Embedding (nativeOrdered A)
      (Hypertournaments.Ramsey.toOrderedNative D order)) :
    OrderedEmbeds A (reindexOrdered D order s) (fun a => s.symm (e a)) := by
  let f : V ↪ Y := e.toFunctionEmbedding.trans s.symm.toEmbedding
  have he := Hypertournaments.Ramsey.preserves_of_orderedEmbedding
    (toHyper A.reduct) D (toLinearOrder A.order) order e
  have hp : Hypertournaments.Preserves (toHyper A.reduct)
      (D.pullback s.toEmbedding) f := by
    intro t
    have ht : (t.trans f).trans s.toEmbedding = t.trans e.toFunctionEmbedding := by
      ext i
      exact s.apply_symm_apply (e (t i))
    change D.orient ((t.trans f).trans s.toEmbedding) = _
    rw [ht]
    exact he t
  refine ⟨(embeds_iff_preserves A.reduct (reindexOrdered D order s).reduct f).mpr
    (by simpa only [reindexOrdered, toHyper_ofHyper] using hp), ?_⟩
  intro a b
  have h := e.map_rel_iff (.inr ()) ![a, b]
  change @LT.lt X order.toLT (e a) (e b) ↔
    @LT.lt V (toLinearOrder A.order).toLT a b at h
  have hlt : A.order.lt a b ↔ @LT.lt X order.toLT (e a) (e b) :=
    (toLinearOrder_lt A.order a b).symm.trans h.symm
  change A.order.lt a b ↔
    @LT.lt X order.toLT (s (s.symm (e a))) (s (s.symm (e b)))
  simpa only [Equiv.apply_symm_apply] using hlt

/-- The full independent Ramsey property, including empty embedding spaces. -/
theorem ramseyOrdered_of_pairCancelling {n : ℕ} (hn : 3 ≤ n)
    (F : FiniteHT n → Prop) (hpc : ∀ D, F D → PairCancelling D) :
    RamseyOrdered F := by
  classical
  intro A B r hA hB hr
  let : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨X, hX, D, order, hD, arrow⟩ :=
    Hypertournaments.Ramsey.exists_ordered_ramsey_witness hn (nativeFamily F)
      (nativeFamily_pairCancelling F hpc) (toHyper A.2.reduct) (toHyper B.2.reduct)
      (toLinearOrder A.2.order) (toLinearOrder B.2.order)
      ((omits_iff F A.2.reduct).mpr hA) ((omits_iff F B.2.reduct).mpr hB) (Fin r)
  let : Finite X := hX
  let : Fintype X := Fintype.ofFinite X
  let s : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let C := reindexOrdered D order s
  refine ⟨⟨Fintype.card X, C⟩, ?_, ?_⟩
  · apply (omits_iff F C.reduct).mp
    simpa only [C, reindexOrdered, toHyper_ofHyper] using
      (Hypertournaments.omits_pullback hD s.toEmbedding)
  · intro color
    obtain ⟨f, hf⟩ := arrow (fun e => color (fun a => s.symm (e a)))
    refine ⟨(fun b => s.symm (f b)),
      orderedEmbeds_of_native_reindex B.2 D order s f, ?_⟩
    by_cases hAB : Nonempty
        (StructuralRamsey.Structure.Embedding (nativeOrdered A.2) (nativeOrdered B.2))
    · let e₀ := Classical.choice hAB
      refine ⟨color (fun a => s.symm (f (e₀ a))), ?_⟩
      intro e he
      exact hf (orderedNativeEmbedding A.2 B.2 e he) e₀
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro e he
      exact False.elim (hAB ⟨orderedNativeEmbedding A.2 B.2 e he⟩)

/-- The full independent ordering property, with one witness for both orders. -/
theorem orderingProperty_of_pairCancelling {n : ℕ} (hn : 3 ≤ n)
    (F : FiniteHT n → Prop) (hpc : ∀ D, F D → PairCancelling D) :
    OrderingProperty F := by
  classical
  intro A hA
  obtain ⟨X, hX, D, hD, hOrders⟩ :=
    Hypertournaments.Ramsey.pair_cancelling_ordering_property hn (nativeFamily F)
      (nativeFamily_pairCancelling F hpc) (toHyper A.2) ((omits_iff F A.2).mpr hA)
  let : Finite X := hX
  let : Fintype X := Fintype.ofFinite X
  let s : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let B := ofHyper (D.pullback s.toEmbedding)
  refine ⟨⟨Fintype.card X, B⟩, ?_, ?_⟩
  · apply (omits_iff F B).mp
    simpa only [B, toHyper_ofHyper] using
      (Hypertournaments.omits_pullback hD s.toEmbedding)
  · intro oa ob
    let targetOrder : LinearOrder X :=
      @LinearOrder.lift' X (Fin (Fintype.card X)) (toLinearOrder ob) s.symm s.symm.injective
    obtain ⟨e⟩ := hOrders (toLinearOrder oa) targetOrder
    let Astar : OrderedHypertournament n (Fin A.1) := ⟨A.2, oa⟩
    have he := orderedEmbeds_of_native_reindex Astar D targetOrder s e
    refine ⟨(fun a => s.symm (e a)), he.1, ?_⟩
    intro a b
    have h := he.2 a b
    change oa.lt a b ↔
      ob.lt (s.symm (s (s.symm (e a)))) (s.symm (s (s.symm (e b)))) at h
    simpa only [Equiv.symm_apply_apply] using h

end

end Bridge

/-- The independently stated introduction link theorem, with no statement edits. -/
theorem intro_link : IntroLinkStatement := by
  intro n hn F hpc
  exact ⟨Bridge.ramseyOrdered_of_pairCancelling hn F hpc,
    Bridge.orderingProperty_of_pairCancelling hn F hpc⟩

end IndependentHypertournaments
