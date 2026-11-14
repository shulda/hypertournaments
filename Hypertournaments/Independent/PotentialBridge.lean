import Hypertournaments.Independent.LinkBridge
import Hypertournaments.PotentialRamsey
import Hypertournaments.PotentialExpansionProperty

/-!
# Proof of the independently stated potential theorem

The statement language is unchanged.  In particular the reduct witness is
chosen before both potentials and both vertex orders.  Carrier changes below
are explicit equivalences, and the final maps retain both named orientations.
Source: article `a732651c134c099ed9de16f49f6aeb0368696678`, `thm:potential`.
-/

namespace IndependentHypertournaments

namespace Bridge

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

private noncomputable abbrev potentialNative {k : ℕ} {V : Type u}
    (A : PotentialExpansion k V) :=
  Hypertournaments.Ramsey.toOrderedPotential (toHyper A.reduct)
    (toHyper A.potential) (toLinearOrder A.order)

private def upperOrdered {k : ℕ} {V : Type u}
    (A : PotentialExpansion k V) : OrderedHypertournament (k + 1) V :=
  ⟨A.reduct, A.order⟩

private def lowerOrdered {k : ℕ} {V : Type u}
    (A : PotentialExpansion k V) : OrderedHypertournament k V :=
  ⟨A.potential, A.order⟩

private def forgetUpperPotentialEmbedding {k : ℕ} {V : Type u} {W : Type v}
    {A : Hypertournaments.Hyper (k + 1) V}
    {B : Hypertournaments.Hyper (k + 1) W}
    {φ : Hypertournaments.Hyper k V} {ψ : Hypertournaments.Hyper k W}
    (oa : LinearOrder V) (ob : LinearOrder W)
    (e : Embedding (Hypertournaments.Ramsey.toOrderedPotential A φ oa)
      (Hypertournaments.Ramsey.toOrderedPotential B ψ ob)) :
    Embedding (Hypertournaments.Ramsey.toOrderedNative A oa)
      (Hypertournaments.Ramsey.toOrderedNative B ob) where
  toFun := e
  injective := e.injective
  map_rel_iff R t := by
    rcases R with u | u
    · exact e.map_rel_iff (.inl true) t
    · exact e.map_rel_iff (.inr ()) t
  map_func F := nomatch F

private noncomputable def potentialNativeEmbedding {k : ℕ}
    {V : Type u} {W : Type v}
    (A : PotentialExpansion k V) (B : PotentialExpansion k W)
    (f : V → W) (hf : PotentialEmbeds A B f) :
    Embedding (potentialNative A) (potentialNative B) :=
  Hypertournaments.Ramsey.liftPotentialEmbedding
    ((isPotential_iff A.reduct A.potential).mp A.compatibility)
    ((isPotential_iff B.reduct B.potential).mp B.compatibility)
    (toLinearOrder A.order) (toLinearOrder B.order)
    (orderedNativeEmbedding (lowerOrdered A) (lowerOrdered B) f ⟨hf.2.1, hf.2.2⟩)

/-- Put a native finite witness on a labelled carrier without selecting any
new potential or imposing a new order condition. -/
private noncomputable def reindexPotential {k : ℕ} {X : Type u} {Y : Type v}
    (D : Hypertournaments.Hyper (k + 1) X) (θ : Hypertournaments.Hyper k X)
    (order : LinearOrder X) (hD : Hypertournaments.IsPotential D θ) (s : Y ≃ X) :
    PotentialExpansion k Y where
  reduct := ofHyper (D.pullback s.toEmbedding)
  potential := ofHyper (θ.pullback s.toEmbedding)
  order := ofLinearOrder (@LinearOrder.lift' Y X order s s.injective)
  compatibility := by
    apply (isPotential_iff _ _).mpr
    simpa only [toHyper_ofHyper] using hD.pullback s.toEmbedding

private theorem potentialEmbeds_of_native_reindex {k : ℕ}
    {V : Type u} {X Y : Type v}
    (A : PotentialExpansion k V)
    (D : Hypertournaments.Hyper (k + 1) X) (θ : Hypertournaments.Hyper k X)
    (order : LinearOrder X) (hD : Hypertournaments.IsPotential D θ) (s : Y ≃ X)
    (e : Embedding (potentialNative A)
      (Hypertournaments.Ramsey.toOrderedPotential D θ order)) :
    PotentialEmbeds A (reindexPotential D θ order hD s)
      (fun a => s.symm (e a)) := by
  have hu := orderedEmbeds_of_native_reindex (upperOrdered A) D order s
    (forgetUpperPotentialEmbedding (toLinearOrder A.order) order e)
  have hl := orderedEmbeds_of_native_reindex (lowerOrdered A) θ order s
    (Hypertournaments.Ramsey.forgetPotentialEmbedding (toLinearOrder A.order) order e)
  exact ⟨hu.1, hl.1, hu.2⟩

private theorem orderData_ext {V : Type u} {a b : LinearOrderData V}
    (h : ∀ x y, a.lt x y ↔ b.lt x y) : a = b := by
  have he : a.lt = b.lt := funext fun x => funext fun y => propext (h x y)
  cases a
  cases b
  cases he
  rfl

private theorem potentialExpansion_ext {k : ℕ} {V : Type u}
    {A B : PotentialExpansion k V} (hr : A.reduct = B.reduct)
    (hp : A.potential = B.potential)
    (ho : ∀ a b, A.order.lt a b ↔ B.order.lt a b) : A = B := by
  have hoe := orderData_ext ho
  cases A
  cases B
  cases hr
  cases hp
  cases hoe
  rfl

/-- The explicit nonvacuity conjunct of the independent target, including
the empty labelled carrier. -/
theorem potentialExpandsEven_of_even {k : ℕ} (hk : Even k) :
    PotentialExpandsEven k := by
  intro A
  constructor
  · intro hA
    obtain ⟨φ, hφ⟩ := (toHyper A.2).exists_potential_fin hk ((isEven_iff A.2).mp hA)
    refine ⟨{
      reduct := A.2
      potential := ofHyper φ
      order := ofLinearOrder inferInstance
      compatibility := ?_ }, rfl⟩
    apply (isPotential_iff _ _).mpr
    simpa only [toHyper_ofHyper] using hφ
  · rintro ⟨Astar, hred⟩
    rw [← hred]
    exact (isEven_iff Astar.reduct).mpr
      ((isPotential_iff _ _).mp Astar.compatibility).isEven

/-- Reindex the genuine native Ramsey witness and translate the coloring
without restricting the independent statement's color domain. -/
theorem potentialRamsey_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    PotentialRamsey k := by
  classical
  intro A B r hr
  let : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨X, hX, D, θ, order, hD, _, arrow⟩ :=
    Hypertournaments.Ramsey.exists_potential_ramsey_witness hk hk2
      (toHyper A.2.reduct) (toHyper B.2.reduct)
      (toHyper A.2.potential) (toHyper B.2.potential)
      ((isPotential_iff _ _).mp A.2.compatibility)
      ((isPotential_iff _ _).mp B.2.compatibility)
      (toLinearOrder A.2.order) (toLinearOrder B.2.order) (Fin r)
  let : Finite X := hX
  let : Fintype X := Fintype.ofFinite X
  let s : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let C : FinitePotentialExpansion k := ⟨_, reindexPotential D θ order hD s⟩
  refine ⟨C, ?_⟩
  intro color
  let χ : Embedding (potentialNative A.2)
      (Hypertournaments.Ramsey.toOrderedPotential D θ order) → Fin r :=
    fun e => color (fun a => s.symm (e a))
  obtain ⟨f, hf⟩ := arrow χ
  let f' : Fin B.1 → Fin C.1 := fun a => s.symm (f a)
  have hff : PotentialEmbeds B.2 C.2 f' :=
    potentialEmbeds_of_native_reindex B.2 D θ order hD s f
  refine ⟨f', hff, ?_⟩
  by_cases hex : ∃ e : Fin A.1 → Fin B.1, PotentialEmbeds A.2 B.2 e
  · obtain ⟨e₀, he₀⟩ := hex
    refine ⟨color (fun a => f' (e₀ a)), ?_⟩
    intro e he
    exact hf (potentialNativeEmbedding A.2 B.2 e he)
      (potentialNativeEmbedding A.2 B.2 e₀ he₀)
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro e he
    exact False.elim (hex ⟨e, he⟩)

/-- The underlying witness is fixed first.  Only after that choice are
arbitrary source and target potentials and arbitrary free orders considered. -/
theorem potentialExpansionProperty_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    PotentialExpansionProperty k := by
  classical
  intro A hA
  obtain ⟨W, hW, B, hB, hWitness⟩ :=
    Hypertournaments.Ramsey.potential_expansion_property hk hk2
      (toHyper A.2) ((isEven_iff A.2).mp hA)
  let : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  let s : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  let B' : FiniteHT (k + 1) := ⟨_, ofHyper (B.pullback s.toEmbedding)⟩
  refine ⟨B', ?_, ?_⟩
  · apply (isEven_iff _).mpr
    simpa only [B', toHyper_ofHyper] using hB.pullback s.toEmbedding
  · intro Astar Bstar hAred hBred
    let ψ : Hypertournaments.Hyper k W :=
      (toHyper Bstar.potential).pullback s.symm.toEmbedding
    let orderB : LinearOrder W :=
      @LinearOrder.lift' W (Fin B'.1) (toLinearOrder Bstar.order) s.symm s.symm.injective
    have hφ : Hypertournaments.IsPotential (toHyper A.2) (toHyper Astar.potential) := by
      simpa only [hAred] using
        (isPotential_iff Astar.reduct Astar.potential).mp Astar.compatibility
    have hψ₀ : Hypertournaments.IsPotential (B.pullback s.toEmbedding)
        (toHyper Bstar.potential) := by
      have h := (isPotential_iff Bstar.reduct Bstar.potential).mp Bstar.compatibility
      simpa only [hBred, B', toHyper_ofHyper] using h
    have hψ : Hypertournaments.IsPotential B ψ :=
      hψ₀.of_equiv_pullback s.symm
    obtain ⟨e⟩ := hWitness (toHyper Astar.potential) (toLinearOrder Astar.order)
      ψ orderB hφ hψ
    have e' : Embedding (potentialNative Astar)
        (Hypertournaments.Ramsey.toOrderedPotential B ψ orderB) := by
      simpa only [potentialNative, hAred] using e
    have hreturn : reindexPotential B ψ orderB hψ s = Bstar := by
      apply potentialExpansion_ext
      · exact hBred.symm
      · change ofHyper (ψ.pullback s.toEmbedding) = Bstar.potential
        have hp : ψ.pullback s.toEmbedding = toHyper Bstar.potential := by
          apply Hypertournaments.Hyper.ext
          intro t
          change (toHyper Bstar.potential).orient
            ((t.trans s.toEmbedding).trans s.symm.toEmbedding) = _
          apply congrArg (toHyper Bstar.potential).orient
          apply Function.Embedding.ext
          intro i
          exact s.symm_apply_apply (t i)
        rw [hp, ofHyper_toHyper]
      · intro a b
        change @LT.lt _ (toLinearOrder Bstar.order).toLT
          (s.symm (s a)) (s.symm (s b)) ↔ Bstar.order.lt a b
        simpa only [s.symm_apply_apply] using toLinearOrder_lt Bstar.order a b
    refine ⟨fun a => s.symm (e' a), ?_⟩
    simpa only [hreturn] using
      potentialEmbeds_of_native_reindex Astar B ψ orderB hψ s e'

end Bridge

/-- The independent target for `thm:potential`, with no definitions replaced
by the project's original theorem signatures. -/
theorem potential : IntroPotentialStatement := by
  intro k hk hmod
  have heven : Even k := Nat.even_iff.mpr hmod
  exact ⟨Bridge.potentialExpandsEven_of_even heven,
    Bridge.potentialRamsey_of_even heven hk,
    Bridge.potentialExpansionProperty_of_even heven hk⟩

end IndependentHypertournaments
