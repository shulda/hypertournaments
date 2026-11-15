import Mathlib.Tactic.Ext
import Hypertournaments.TwoPadSlice

/-!
# Naturality of intrinsic two-pad tuples under arbitrary vertex embeddings

For any injective embedding of ambient vertex sets, forming a two-pad
tuple and then embedding it is the same as first embedding the old
vertices and pads and then forming the two-pad tuple.

This is a purely geometric identity. It is needed to transfer the
orientation-recovery property from a lifted source to a hypothetical
higher-arity ordinary amalgam, without assuming any order on its
vertices or identifying an undefined tuple with a defined one.
-/

namespace Hypertournaments

/-- Disjointness of one pad from the old vertex set survives an
arbitrary injective embedding of the ambient universe. -/
theorem twoPad_not_mem_range_after_embedding
    {W V Z : Type*} (g : W ↪ V) (j : V ↪ Z)
    (p : V) (hp : p ∉ Set.range g) :
    j p ∉ Set.range (g.trans j) := by
  rintro ⟨x, hx⟩
  change j (g x) = j p at hx
  exact hp ⟨x, j.injective hx⟩

/-- Exact equality of the two-pad tuples after embedding the ambient
vertex set. All source and target tuples remain genuinely injective. -/
theorem twoPadSliceTuple_natural
    {n : ℕ} {W V Z : Type*} (g : W ↪ V) (j : V ↪ Z)
    (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin n ↪ W) :
    twoPadSliceTuple (g.trans j) (j p) (j q)
        (twoPad_not_mem_range_after_embedding g j p hp)
        (twoPad_not_mem_range_after_embedding g j q hq)
        (fun h => hpq (j.injective h)) t =
      (twoPadSliceTuple g p q hp hq hpq t).trans j := by
  ext k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun l => ?_) i) k
  · simp [twoPadSliceTuple]
  · simp [twoPadSliceTuple]
  · simp [twoPadSliceTuple]

end Hypertournaments
