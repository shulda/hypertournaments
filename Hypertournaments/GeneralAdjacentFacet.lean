import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.GeneralFacetSwap

/-!
# Generic adjacent-transposition law for all oriented facets

A swap of neighboring coordinates in an (n+1)-tuple exchanges the
two neighboring deleted facets literally. All other facets have their
raw orientation reversed, by the generic restricted-swap theorem.
The parity normalization therefore complements the entire facet
packet and permutes its entries, in every arity.

No arity-specific finite lookup tables or external axioms are used.
-/

namespace Hypertournaments

/-- Swap p with p+1 in Fin (n+1). -/
def adjacentSwapCoord {n : ℕ} (p : Fin n) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap p.castSucc p.succ

/-- After deleting the left swapped coordinate, an adjacent swap
gives exactly the facet obtained by deleting the right coordinate. -/
theorem adjacent_swap_succAbove_left
    {n : ℕ} (p : Fin n) (i : Fin n) :
    (adjacentSwapCoord p) (p.castSucc.succAbove i) =
      p.succ.succAbove i := by
  by_cases hlt : i < p
  · have hc : i.castSucc < p.castSucc := by
      change i.val < p.val
      exact hlt
    have hd : i.castSucc < p.succ := by
      change i.val < p.val + 1
      omega
    have hleft :
        p.castSucc.succAbove i = i.castSucc :=
      Fin.succAbove_of_castSucc_lt p.castSucc i hc
    have hright :
        p.succ.succAbove i = i.castSucc :=
      Fin.succAbove_of_castSucc_lt p.succ i hd
    rw [hleft, hright]
    exact Equiv.swap_apply_of_ne_of_ne
      (ne_of_lt hc) (ne_of_lt hd)
  · by_cases heq : i = p
    · subst i
      have hc : p.castSucc ≤ p.castSucc := le_refl _
      have hd : p.castSucc < p.succ := by
        change p.val < p.val + 1
        omega
      have hleft :
          p.castSucc.succAbove p = p.succ :=
        Fin.succAbove_of_le_castSucc p.castSucc p hc
      have hright :
          p.succ.succAbove p = p.castSucc :=
        Fin.succAbove_of_castSucc_lt p.succ p hd
      rw [hleft, hright]
      exact Equiv.swap_apply_right p.castSucc p.succ
    · have hgt : p.val < i.val := by
        have hnot : ¬ i.val < p.val := hlt
        have hneq : i.val ≠ p.val := by
          intro he
          exact heq (Fin.ext he)
        omega
      have hc : p.castSucc ≤ i.castSucc := by
        change p.val ≤ i.val
        omega
      have hd : p.succ ≤ i.castSucc := by
        change p.val + 1 ≤ i.val
        omega
      have hleft :
          p.castSucc.succAbove i = i.succ :=
        Fin.succAbove_of_le_castSucc p.castSucc i hc
      have hright :
          p.succ.succAbove i = i.succ :=
        Fin.succAbove_of_le_castSucc p.succ i hd
      rw [hleft, hright]
      have hn1 : i.succ ≠ p.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        change i.val + 1 = p.val at hv
        omega
      have hn2 : i.succ ≠ p.succ := by
        intro he
        have hv := congrArg Fin.val he
        change i.val + 1 = p.val + 1 at hv
        omega
      exact Equiv.swap_apply_of_ne_of_ne hn1 hn2

/-- Symmetric endpoint deletion identity. -/
theorem adjacent_swap_succAbove_right
    {n : ℕ} (p : Fin n) (i : Fin n) :
    (adjacentSwapCoord p) (p.succ.succAbove i) =
      p.castSucc.succAbove i := by
  have h := congrArg (adjacentSwapCoord p)
    (adjacent_swap_succAbove_left p i)
  simpa only [adjacentSwapCoord, Equiv.swap_apply_self] using h.symm

/-- The first swapped facet is literally the second original facet. -/
theorem facet_adjacent_swap_left
    {n : ℕ} {V : Type*} (f : Fin (n + 1) ↪ V)
    (p : Fin n) :
    facet ((adjacentSwapCoord p).toEmbedding.trans f) p.castSucc =
      facet f p.succ := by
  ext i
  change f ((adjacentSwapCoord p) (p.castSucc.succAbove i)) =
    f (p.succ.succAbove i)
  exact congrArg f (adjacent_swap_succAbove_left p i)

/-- The second swapped facet is literally the first original facet. -/
theorem facet_adjacent_swap_right
    {n : ℕ} {V : Type*} (f : Fin (n + 1) ↪ V)
    (p : Fin n) :
    facet ((adjacentSwapCoord p).toEmbedding.trans f) p.succ =
      facet f p.castSucc := by
  ext i
  change f ((adjacentSwapCoord p) (p.succ.succAbove i)) =
    f (p.castSucc.succAbove i)
  exact congrArg f (adjacent_swap_succAbove_right p i)

/-- Adjacent indices have opposite normalization parity. -/
theorem bool_xor_parity_adjacent
    {n : ℕ} (p : Fin n) (b : Bool) :
    Bool.xor b (decide (p.castSucc.val % 2 = 1)) =
      !(Bool.xor b (decide (p.succ.val % 2 = 1))) := by
  by_cases hp : p.val % 2 = 1
  · have hn : (p.val + 1) % 2 ≠ 1 := by omega
    cases b <;> simp [Fin.val_succ, hp, hn]
  · have hn : (p.val + 1) % 2 = 1 := by omega
    cases b <;> simp [Fin.val_succ, hp, hn]

/-- Left endpoint of an adjacent transposition complements the
normalized sign at the corresponding opposite facet. -/
theorem normalizedFacet_adjacent_swap_left
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) (p : Fin n) :
    normalizedFacet A ((adjacentSwapCoord p).toEmbedding.trans f)
      p.castSucc = !(normalizedFacet A f p.succ) := by
  unfold normalizedFacet
  rw [facet_adjacent_swap_left]
  exact bool_xor_parity_adjacent p (A.orient (facet f p.succ))

/-- Right endpoint has the same complement law. -/
theorem normalizedFacet_adjacent_swap_right
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) (p : Fin n) :
    normalizedFacet A ((adjacentSwapCoord p).toEmbedding.trans f)
      p.succ = !(normalizedFacet A f p.castSucc) := by
  unfold normalizedFacet
  rw [facet_adjacent_swap_right]
  have h := bool_xor_parity_adjacent p
    (A.orient (facet f p.castSucc))
  simpa only [Bool.not_not] using (congrArg Bool.not h).symm

/-- Uniform all-arity normalized facet relabeling under adjacent
coordinate swaps. This is the key geometric part of local-index
invariance and holds for arbitrary hypertournaments. -/
theorem normalizedFacet_adjacent_swap
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) (p : Fin n)
    (i : Fin (n + 1)) :
    normalizedFacet A ((adjacentSwapCoord p).toEmbedding.trans f) i =
      !(normalizedFacet A f ((adjacentSwapCoord p) i)) := by
  by_cases hleft : i = p.castSucc
  · subst i
    rw [show adjacentSwapCoord p p.castSucc = p.succ by
      exact Equiv.swap_apply_left p.castSucc p.succ]
    exact normalizedFacet_adjacent_swap_left A f p
  · by_cases hright : i = p.succ
    · subst i
      rw [show adjacentSwapCoord p p.succ = p.castSucc by
        exact Equiv.swap_apply_right p.castSucc p.succ]
      exact normalizedFacet_adjacent_swap_right A f p
    · have hfix : adjacentSwapCoord p i = i :=
        Equiv.swap_apply_of_ne_of_ne hleft hright
      rw [hfix]
      have hab : p.castSucc ≠ p.succ := by
        intro he
        have hv := congrArg Fin.val he
        change p.val = p.val + 1 at hv
        omega
      exact normalizedFacet_swap_away A f p.castSucc p.succ i
        hleft hright hab

end Hypertournaments
