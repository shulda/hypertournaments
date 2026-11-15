import Hypertournaments.OddToggleP1Homogeneous
import Hypertournaments.FinitePresentation
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Order.RelClasses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# Intrinsic transitive tournaments and linear orders

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the small-arity paragraph of `thm:constrained-classification`.
The central-only binary palette is exactly transitivity. Its intrinsic
orientation recovers a linear order on any carrier, without finiteness.
-/

namespace Hypertournaments

universe u v

/-- The forward binary orientation, expressed without any ambient order. -/
def Hyper.binaryLT {V : Type u} (A : Hyper 2 V) (x y : V) : Prop :=
  ∃ h : x ≠ y, A.orient (Function.Embedding.embFinTwo h) = false

theorem Hyper.binary_orient_reverse {V : Type u} (A : Hyper 2 V)
    {x y : V} (hxy : x ≠ y) (hyx : y ≠ x) :
    A.orient (Function.Embedding.embFinTwo hyx) =
      !A.orient (Function.Embedding.embFinTwo hxy) := by
  have ht : Function.Embedding.embFinTwo hyx =
      (Equiv.swap (0 : Fin 2) 1).toEmbedding.trans
        (Function.Embedding.embFinTwo hxy) := by
    ext i
    fin_cases i <;> simp [Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one]
  rw [ht]
  exact A.swap_flip _ 0 1 (by decide)

/-- Every actual ordered edge reads the intrinsic strict relation. -/
theorem Hyper.binaryLT_iff_orient {V : Type u} (A : Hyper 2 V)
    (t : Fin 2 ↪ V) : A.binaryLT (t 0) (t 1) ↔ A.orient t = false := by
  have hne : t 0 ≠ t 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (t.injective h)
  have ht (h : t 0 ≠ t 1) : Function.Embedding.embFinTwo h = t := by
    ext i
    fin_cases i <;> simp [Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one]
  constructor
  · rintro ⟨h, hb⟩
    simpa only [ht h] using hb
  · intro hb
    exact ⟨hne, by simpa only [ht hne] using hb⟩

theorem Hyper.binaryLT_irrefl {V : Type u} (A : Hyper 2 V) (x : V) :
    ¬ A.binaryLT x x := by
  rintro ⟨h, _⟩
  exact h rfl

theorem Hyper.binaryLT_asymm {V : Type u} (A : Hyper 2 V) {x y : V}
    (hxy : A.binaryLT x y) : ¬ A.binaryLT y x := by
  rcases hxy with ⟨hne, hb⟩
  rintro ⟨hne', hb'⟩
  have h := A.binary_orient_reverse hne hne'
  simp only [hb, hb', Bool.not_false] at h
  contradiction

theorem Hyper.binaryLT_or_reverse {V : Type u} (A : Hyper 2 V) {x y : V}
    (hne : x ≠ y) : A.binaryLT x y ∨ A.binaryLT y x := by
  cases hb : A.orient (Function.Embedding.embFinTwo hne) with
  | false => exact Or.inl ⟨hne, hb⟩
  | true =>
    exact Or.inr ⟨hne.symm, by simpa only [hb, Bool.not_true] using
      (A.binary_orient_reverse hne hne.symm)⟩

/-- In a central-only binary packet, two forward successive edges force
the forward long edge. The forbidden alternative is a constant normalized packet. -/
theorem Hyper.binary_facet_trans {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) (f : Fin 3 ↪ V)
    (h0 : A.orient (facet f 0) = false)
    (h2 : A.orient (facet f 2) = false) :
    A.orient (facet f 1) = false := by
  cases h1 : A.orient (facet f 1) with
  | false => rfl
  | true =>
    have hz : localIndex A f = 0 :=
      (localIndex_zero_iff_normalized_constant A f).mpr ⟨false, by
        intro i
        fin_cases i <;> simp [normalizedFacet, h0, h1, h2]⟩
    exact False.elim (by simpa [hz] using hA f)

theorem Hyper.binaryLT_trans {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) :
    ∀ ⦃x y z : V⦄, A.binaryLT x y → A.binaryLT y z → A.binaryLT x z := by
  intro x y z hxy hyz
  have hneXY : x ≠ y := hxy.choose
  have hneYZ : y ≠ z := hyz.choose
  have hneXZ : x ≠ z := by
    intro h
    subst z
    exact A.binaryLT_asymm hxy hyz
  let f : Fin 3 ↪ V := ⟨![x, y, z], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have h0 : A.orient (facet f 0) = false :=
    (A.binaryLT_iff_orient _).mp (by change A.binaryLT y z; exact hyz)
  have h2 : A.orient (facet f 2) = false :=
    (A.binaryLT_iff_orient _).mp (by change A.binaryLT x y; exact hxy)
  have h1 := A.binary_facet_trans hA f h0 h2
  have h := (A.binaryLT_iff_orient (facet f 1)).mpr h1
  exact h

/-- The central-only binary local condition is precisely transitivity. -/
theorem admissible_one_iff_binaryLT_trans {V : Type u} (A : Hyper 2 V) :
    Admissible ({1} : Set ℕ) A ↔ IsTrans V A.binaryLT := by
  constructor
  · intro hA
    exact ⟨fun _ _ _ hxy hyz => A.binaryLT_trans hA hxy hyz⟩
  · intro htrans f
    have hle := localIndex_le_central A f
    have hne : localIndex A f ≠ 0 := by
      intro hz
      obtain ⟨b, hb⟩ := (localIndex_zero_iff_normalized_constant A f).mp hz
      have h0 := hb (0 : Fin 3)
      have h1 := hb (1 : Fin 3)
      have h2 := hb (2 : Fin 3)
      cases b with
      | false =>
        have hxy : A.binaryLT (f 0) (f 1) := by
          apply (A.binaryLT_iff_orient (facet f 2)).mpr
          simpa [normalizedFacet] using h2
        have hyz : A.binaryLT (f 1) (f 2) := by
          apply (A.binaryLT_iff_orient (facet f 0)).mpr
          simpa [normalizedFacet] using h0
        have hxz := (A.binaryLT_iff_orient (facet f 1)).mp (htrans.trans _ _ _ hxy hyz)
        simp [normalizedFacet, hxz] at h1
      | true =>
        have hxy : ¬ A.binaryLT (f 0) (f 1) := by
          intro h
          have ht := (A.binaryLT_iff_orient (facet f 2)).mp (by exact h)
          simp [normalizedFacet, ht] at h2
        have hyz : ¬ A.binaryLT (f 1) (f 2) := by
          intro h
          have ht := (A.binaryLT_iff_orient (facet f 0)).mp (by simpa [facet] using h)
          simp [normalizedFacet, ht] at h0
        have hyx : A.binaryLT (f 1) (f 0) :=
          (A.binaryLT_or_reverse (by exact f.injective.ne (by decide))).resolve_left hxy
        have hzy : A.binaryLT (f 2) (f 1) :=
          (A.binaryLT_or_reverse (by exact f.injective.ne (by decide))).resolve_left hyz
        have hxz : A.binaryLT (f 0) (f 2) := by
          apply (A.binaryLT_iff_orient (facet f 1)).mpr
          simpa [normalizedFacet] using h1
        exact A.binaryLT_asymm hxz (htrans.trans _ _ _ hzy hyx)
    have hi : localIndex A f = 1 := by
      change localIndex A f ≤ 1 at hle
      omega
    simpa only [Set.mem_singleton_iff] using hi

/-- The orientation canonically recovers the order; no carrier finiteness is used. -/
@[instance_reducible] noncomputable def Hyper.binaryLinearOrder {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) : LinearOrder V := by
  classical
  letI : IsStrictTotalOrder V A.binaryLT := {
    irrefl := A.binaryLT_irrefl
    trans := fun _ _ _ hxy hyz => A.binaryLT_trans hA hxy hyz
    trichotomous := fun x y hxy hyx => by
      by_contra hne
      exact (A.binaryLT_or_reverse hne).elim hxy hyx }
  exact linearOrderOfSTO A.binaryLT

theorem Hyper.binaryLinearOrder_lt_iff {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) (x y : V) :
    @LT.lt V (A.binaryLinearOrder hA).toLT x y ↔ A.binaryLT x y := Iff.rfl

/-- The standard constant-sign model reads precisely its defining linear order. -/
theorem binary_order_model_orient_false_iff {V : Type u} [LinearOrder V]
    (t : Fin 2 ↪ V) :
    (Hyper.fromOrderedSigns (n := 2) (fun _ : Finset V => false)).orient t = false ↔
      t 0 < t 1 := by
  let M : Hyper 2 V := Hyper.fromOrderedSigns (fun _ => false)
  by_cases hlt : t 0 < t 1
  · have ht : StrictMono (t : Fin 2 → V) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    rw [fromOrderedSigns_orient_strictMono _ _ ht]
    simp [hlt]
  · have hne : t 0 ≠ t 1 :=
      fun h => (by decide : (0 : Fin 2) ≠ 1) (t.injective h)
    have hgt : t 1 < t 0 := (lt_or_gt_of_ne hne).resolve_left hlt
    let s := (Equiv.swap (0 : Fin 2) 1).toEmbedding.trans t
    have hs : StrictMono (s : Fin 2 → V) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [s]
    have hb := fromOrderedSigns_orient_strictMono (fun _ : Finset V => false) s hs
    have hn : M.orient t ≠ false := by
      intro he
      have hswap := M.swap_flip t 0 1 (by decide)
      change M.orient s = false at hb
      rw [hswap, he] at hb
      contradiction
    exact iff_of_false hn hlt

/-- The intrinsic relation of a constant-sign model is its original order. -/
theorem binary_order_model_binaryLT_iff {V : Type u} [LinearOrder V] (x y : V) :
    (Hyper.fromOrderedSigns (n := 2) (fun _ : Finset V => false)).binaryLT x y ↔ x < y := by
  constructor
  · rintro ⟨hne, hb⟩
    have h := (binary_order_model_orient_false_iff
      (Function.Embedding.embFinTwo hne)).mp hb
    simpa only [Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one] using h
  · intro hlt
    refine ⟨ne_of_lt hlt, (binary_order_model_orient_false_iff _).mpr ?_⟩
    simpa only [Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one] using hlt

/-- Every linear order gives a model of the central-only binary palette. -/
theorem binary_order_model_admissible {V : Type u} [LinearOrder V] :
    Admissible ({1} : Set ℕ)
      (Hyper.fromOrderedSigns (n := 2) (fun _ : Finset V => false)) := by
  apply (admissible_one_iff_binaryLT_trans _).mpr
  refine ⟨fun x y z hxy hyz => ?_⟩
  exact (binary_order_model_binaryLT_iff x z).mpr
    (lt_trans ((binary_order_model_binaryLT_iff x y).mp hxy)
      ((binary_order_model_binaryLT_iff y z).mp hyz))

theorem Hyper.binaryLinearOrder_orient_false_iff {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) (t : Fin 2 ↪ V) :
    A.orient t = false ↔ @LT.lt V (A.binaryLinearOrder hA).toLT (t 0) (t 1) :=
  (A.binaryLT_iff_orient t).symm

/-- Reconstruction recovers all ordered edges, not just increasing edges. -/
theorem Hyper.binaryLinearOrder_model_orient {V : Type u} (A : Hyper 2 V)
    (hA : Admissible ({1} : Set ℕ) A) (t : Fin 2 ↪ V) :
    A.orient t =
      (@Hyper.fromOrderedSigns 2 V (A.binaryLinearOrder hA) (fun _ => false)).orient t := by
  let : LinearOrder V := A.binaryLinearOrder hA
  have h := (A.binaryLinearOrder_orient_false_iff hA t).trans
    (binary_order_model_orient_false_iff t).symm
  cases ha : A.orient t <;>
    cases hb : (Hyper.fromOrderedSigns (n := 2) (fun _ : Finset V => false)).orient t <;>
      simp_all

/-- Intrinsic embeddings between transitive tournaments are precisely the
strictly monotone injections between their reconstructed linear orders. -/
theorem preserves_iff_binaryLinearOrder_strictMono
    {V : Type u} {W : Type v} (A : Hyper 2 V) (B : Hyper 2 W)
    (hA : Admissible ({1} : Set ℕ) A) (hB : Admissible ({1} : Set ℕ) B)
    (e : V ↪ W) :
    Preserves A B e ↔
      @StrictMono V W (A.binaryLinearOrder hA).toPreorder
        (B.binaryLinearOrder hB).toPreorder e := by
  let : LinearOrder V := A.binaryLinearOrder hA
  let : LinearOrder W := B.binaryLinearOrder hB
  constructor
  · intro he x y hxy
    rcases hxy with ⟨hne, hb⟩
    have hne' : e x ≠ e y := fun h => hne (e.injective h)
    refine ⟨hne', ?_⟩
    have ht : (Function.Embedding.embFinTwo hne).trans e =
        Function.Embedding.embFinTwo hne' := by
      ext i
      fin_cases i <;> simp [Function.Embedding.embFinTwo_apply_zero,
        Function.Embedding.embFinTwo_apply_one]
    have h := he (Function.Embedding.embFinTwo hne)
    rw [ht] at h
    exact h.trans hb
  · intro he t
    have ha := A.binaryLinearOrder_orient_false_iff hA t
    have hb := B.binaryLinearOrder_orient_false_iff hB (t.trans e)
    have h : A.orient t = false ↔ B.orient (t.trans e) = false :=
      ha.trans (he.lt_iff_lt.symm.trans hb.symm)
    cases hta : A.orient t <;> cases htb : B.orient (t.trans e) <;> simp_all

end Hypertournaments
