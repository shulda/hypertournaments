import Hypertournaments.Automorphism
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ext

/-!
# Intrinsic links at a fixed vertex

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer`. The point is prepended to actual injective tuples;
no vertex order or evenness of the upper structure is assumed.
-/

universe u v

namespace Hypertournaments

/-- Prepend a point outside the image of the vertex embedding. -/
def onePointTuple {r : ℕ} {V : Type u} {W : Type v}
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e) (t : Fin r ↪ V) :
    Fin (r + 1) ↪ W :=
  Fin.Embedding.cons (t.trans e) (by
    rintro ⟨i, hi⟩
    exact hp ⟨t i, hi⟩)

@[simp] theorem onePointTuple_zero {r : ℕ} {V : Type u} {W : Type v}
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e) (t : Fin r ↪ V) :
    onePointTuple e p hp t 0 = p := rfl

@[simp] theorem onePointTuple_succ {r : ℕ} {V : Type u} {W : Type v}
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e) (t : Fin r ↪ V) (i : Fin r) :
    onePointTuple e p hp t i.succ = e (t i) := rfl

def onePointLiftPerm {r : ℕ} (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

@[simp] theorem onePointLiftPerm_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    onePointLiftPerm σ 0 = 0 := by simp [onePointLiftPerm]

@[simp] theorem onePointLiftPerm_succ {r : ℕ} (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    onePointLiftPerm σ i.succ = (σ i).succ := by simp [onePointLiftPerm]

theorem onePointLiftPerm_sign {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    (onePointLiftPerm σ).sign = σ.sign := by
  simp [onePointLiftPerm, Equiv.Perm.decomposeFin.symm_sign]

theorem onePointTuple_reordered {r : ℕ} {V : Type u} {W : Type v}
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e) (t : Fin r ↪ V)
    (σ : Equiv.Perm (Fin r)) :
    onePointTuple e p hp (σ.toEmbedding.trans t) =
      (onePointLiftPerm σ).toEmbedding.trans (onePointTuple e p hp t) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Restriction to the link along any injection avoiding the distinguished point. -/
def Hyper.onePointSlice {r : ℕ} {V : Type u} {W : Type v}
    (B : Hyper (r + 1) W) (e : V ↪ W) (p : W) (hp : p ∉ Set.range e) : Hyper r V where
  orient t := B.orient (onePointTuple e p hp t)
  swap_flip t i j hij := by
    rw [onePointTuple_reordered, B.orient_perm, onePointLiftPerm_sign,
      Equiv.Perm.sign_swap hij]
    simp [Units.ext_iff]

def pointComplementEmbedding {W : Type v} (p : W) : {x : W // x ≠ p} ↪ W :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem point_not_mem_complement {W : Type v} (p : W) :
    p ∉ Set.range (pointComplementEmbedding p) := by
  rintro ⟨x, hx⟩
  exact x.property hx

/-- The full intrinsic link on the complement of the distinguished vertex. -/
def Hyper.onePointLink {r : ℕ} {W : Type v} (B : Hyper (r + 1) W) (p : W) :
    Hyper r {x : W // x ≠ p} :=
  B.onePointSlice (pointComplementEmbedding p) p (point_not_mem_complement p)

/-- An automorphism fixing the distinguished point restricts to its complement. -/
def Hyper.Aut.complementPerm {r : ℕ} {W : Type v} {B : Hyper (r + 1) W}
    (g : B.Aut) (p : W) (hgp : (g : Equiv.Perm W) p = p) :
    Equiv.Perm {x : W // x ≠ p} := by
  have hginv : (g : Equiv.Perm W).symm p = p := by
    apply (g : Equiv.Perm W).injective
    simpa using hgp.symm
  exact {
    toFun := fun x => ⟨(g : Equiv.Perm W) x, by
      intro hx
      apply x.property
      exact (g : Equiv.Perm W).injective (hx.trans hgp.symm)⟩
    invFun := fun x => ⟨(g : Equiv.Perm W).symm x, by
      intro hx
      apply x.property
      exact (g : Equiv.Perm W).symm.injective (hx.trans hginv.symm)⟩
    left_inv := fun x => Subtype.ext ((g : Equiv.Perm W).symm_apply_apply x)
    right_inv := fun x => Subtype.ext ((g : Equiv.Perm W).apply_symm_apply x) }

@[simp] theorem Hyper.Aut.complementPerm_apply {r : ℕ} {W : Type v}
    {B : Hyper (r + 1) W} (g : B.Aut) (p : W) (hgp : (g : Equiv.Perm W) p = p)
    (x : {x : W // x ≠ p}) : (g.complementPerm p hgp x : W) = (g : Equiv.Perm W) x := rfl

/-- The restricted permutation is an actual automorphism of the full link. -/
def Hyper.Aut.onePointLink {r : ℕ} {W : Type v} {B : Hyper (r + 1) W}
    (g : B.Aut) (p : W) (hgp : (g : Equiv.Perm W) p = p) : (B.onePointLink p).Aut := by
  let σ := g.complementPerm p hgp
  refine ⟨σ, ?_⟩
  intro t
  have ht : onePointTuple (pointComplementEmbedding p) p (point_not_mem_complement p)
      (t.trans σ.toEmbedding) =
      (onePointTuple (pointComplementEmbedding p) p (point_not_mem_complement p) t).trans
        (g : Equiv.Perm W).toEmbedding := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hgp.symm
    · rfl
  change B.orient (onePointTuple _ p _ (t.trans σ.toEmbedding)) = _
  rw [ht]
  exact g.preserves _

end Hypertournaments
