import Hypertournaments.EvenCone
import Mathlib.Tactic.Choose

/-!
# Naturality of the even one-point cone

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer`. Checking the old tuples and root-first tuples
checks all tuples, so every lower embedding extends by fixing the root.
-/

namespace Hypertournaments

universe u v

theorem exists_tuple_of_option_ne_none {k : ℕ} {V : Type u}
    (f : Fin k ↪ Option V) (h : ∀ i, f i ≠ none) :
    ∃ t : Fin k ↪ V, t.trans Function.Embedding.some = f := by
  classical
  have hv : ∀ i, ∃ x, f i = some x := by
    intro i
    cases he : f i with
    | none => exact (h i he).elim
    | some x => exact ⟨x, rfl⟩
  choose t ht using hv
  let te : Fin k ↪ V := ⟨t, fun i j hij =>
    f.injective ((ht i).trans ((congrArg some hij).trans (ht j).symm))⟩
  refine ⟨te, ?_⟩
  apply Function.Embedding.ext
  intro i
  exact (ht i).symm

theorem exists_root_first_tuple {r : ℕ} {V : Type u}
    (f : Fin (r + 1) ↪ Option V) (h : f 0 = none) :
    ∃ t : Fin r ↪ V,
      onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t = f := by
  let tail := (Fin.succEmb r).trans f
  have hn (i : Fin r) : tail i ≠ none := by
    intro hi
    have he : i.succ = (0 : Fin (r + 1)) := f.injective (hi.trans h.symm)
    exact (Fin.succ_ne_zero i) he
  obtain ⟨t, ht⟩ := exists_tuple_of_option_ne_none tail hn
  refine ⟨t, ?_⟩
  apply Function.Embedding.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h.symm
  · exact congrArg (fun e : Fin r ↪ Option V => e j) ht

theorem optionMap_onePointTuple {r : ℕ} {V : Type u} {W : Type v}
    (e : V ↪ W) (t : Fin r ↪ V) :
    (onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t).trans
        (Function.Embedding.optionMap e) =
      onePointTuple Function.Embedding.some none (none_not_mem_someRange W) (t.trans e) := by
  apply Function.Embedding.ext
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

/-- Root-first and root-avoiding equations determine preservation on the
whole option carrier, without any ambient order or finiteness assumption. -/
theorem preserves_option_of_old_and_root {r : ℕ} {V : Type u} {W : Type v}
    (A : Hyper (r + 1) (Option V)) (B : Hyper (r + 1) (Option W)) (e : V ↪ W)
    (hold : ∀ t : Fin (r + 1) ↪ V,
      B.orient ((t.trans Function.Embedding.some).trans (Function.Embedding.optionMap e)) =
        A.orient (t.trans Function.Embedding.some))
    (hroot : ∀ t : Fin r ↪ V,
      B.orient ((onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t).trans
        (Function.Embedding.optionMap e)) =
      A.orient (onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t)) :
    Preserves A B (Function.Embedding.optionMap e) := by
  classical
  intro f
  by_cases hnone : ∃ j, f j = none
  · obtain ⟨j, hj⟩ := hnone
    let σ := Equiv.swap (0 : Fin (r + 1)) j
    let g := σ.toEmbedding.trans f
    have hg : g 0 = none := by
      change f (Equiv.swap 0 j 0) = none
      rw [Equiv.swap_apply_left]
      exact hj
    obtain ⟨t, ht⟩ := exists_root_first_tuple g hg
    have hh := hroot t
    rw [ht] at hh
    have hcomp : g.trans (Function.Embedding.optionMap e) =
        σ.toEmbedding.trans (f.trans (Function.Embedding.optionMap e)) := by
      apply Function.Embedding.ext
      intro i
      rfl
    change B.orient (g.trans (Function.Embedding.optionMap e)) = A.orient g at hh
    rw [hcomp, B.orient_perm, A.orient_perm] at hh
    by_cases hs : σ.sign = (1 : ℤˣ)
    · simpa only [hs, ite_true] using hh
    · have hn : (!B.orient (f.trans (Function.Embedding.optionMap e))) = !A.orient f := by
        simpa only [hs, ite_false] using hh
      exact Bool.not_inj hn
  · obtain ⟨t, ht⟩ := exists_tuple_of_option_ne_none f (by
      intro i hi
      exact hnone ⟨i, hi⟩)
    simpa only [ht] using hold t

/-- Every intrinsic lower embedding extends to the even cones by fixing
the new root. No order-preservation hypothesis is introduced. -/
theorem Hyper.evenCone_preserves {r : ℕ} {V : Type u} {W : Type v}
    [Finite V] [Finite W] (A : Hyper r V) (B : Hyper r W)
    (hr : Even r) (e : V ↪ W) (he : Preserves A B e) :
    Preserves (A.evenCone hr) (B.evenCone hr) (Function.Embedding.optionMap e) := by
  apply preserves_option_of_old_and_root
  · intro t
    have ht : (t.trans Function.Embedding.some).trans (Function.Embedding.optionMap e) =
        (t.trans e).trans Function.Embedding.some := by
      apply Function.Embedding.ext
      intro i
      rfl
    rw [ht, Hyper.evenCone_old_orient, Hyper.evenCone_old_orient]
    exact A.coboundary_preserves B hr e he t
  · intro t
    rw [optionMap_onePointTuple, Hyper.evenCone_root_orient, Hyper.evenCone_root_orient]
    exact he t

end Hypertournaments
