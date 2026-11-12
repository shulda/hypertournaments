import Hypertournaments.OddToggleP3SixRepeatEdges

/-!
# Exact isolated even/odd position witnesses from six edge flags

The kernel-certified six-edge selector says that, when at most
two of the first six adjacent block edges repeat a block label,
there are candidate old vertex positions of both deletion
parities with all incident adjacent edges nonrepeated.

We expose those positions explicitly: a coordinate i among the
first six is isolated when its right edge is good and either
i=0 or its left edge is also good. The output is a pair of
actual Fin 6 indices of opposite parity with these properties.

The next independent monotone-label lemma converts these
local edge conditions into global singleton block labels.
This file contains finite combinatorics only, not side age.
-/

namespace Hypertournaments

/-- The right edge is good and the left edge, when present,
is also good. (There are six edges and seven vertices.) -/
def p3SixEdge_isolated_position
    (bad : Fin 6 → Bool) (i : Fin 6) : Prop :=
  bad i = false ∧
    (i.val = 0 ∨
      ∃ pred : Fin 6, pred.val+1=i.val ∧ bad pred = false)

/-- With at most two bad edges, some isolated candidate vertex
has even position and another isolated candidate has odd
position, both among the first six vertices. -/
theorem p3SixEdge_isolated_even_odd_witnesses
    (bad : Fin 6 → Bool)
    (hbad : (Finset.univ.filter (fun i : Fin 6 => bad i = true)).card ≤ 2) :
    ∃ i j : Fin 6,
      i.val%2=0 ∧ j.val%2=1 ∧
      p3SixEdge_isolated_position bad i ∧
      p3SixEdge_isolated_position bad j := by
  obtain ⟨he, ho⟩ := p3SixEdgeFlags_two_parity_singletons bad hbad
  have heven :
      ∃ i : Fin 6, i.val%2=0 ∧ p3SixEdge_isolated_position bad i := by
    rcases he with h0 | h2 | h4
    · refine ⟨0, by decide, ?_⟩
      exact ⟨h0, Or.inl rfl⟩
    · refine ⟨2, by decide, ?_⟩
      exact ⟨h2.2, Or.inr ⟨1, by decide, h2.1⟩⟩
    · refine ⟨4, by decide, ?_⟩
      exact ⟨h4.2, Or.inr ⟨3, by decide, h4.1⟩⟩
  have hodd :
      ∃ i : Fin 6, i.val%2=1 ∧ p3SixEdge_isolated_position bad i := by
    rcases ho with h1 | h3 | h5
    · refine ⟨1, by decide, ?_⟩
      exact ⟨h1.2, Or.inr ⟨0, by decide, h1.1⟩⟩
    · refine ⟨3, by decide, ?_⟩
      exact ⟨h3.2, Or.inr ⟨2, by decide, h3.1⟩⟩
    · refine ⟨5, by decide, ?_⟩
      exact ⟨h5.2, Or.inr ⟨4, by decide, h5.1⟩⟩
  obtain ⟨i, hi, hIi⟩ := heven
  obtain ⟨j, hj, hIj⟩ := hodd
  exact ⟨i, j, hi, hj, hIi, hIj⟩

end Hypertournaments
