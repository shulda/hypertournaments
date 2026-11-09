import Hypertournaments.NegativeModuloOddToggle

/-!
# The fixed six-vertex graph core of the odd toggle-zero obstruction

For all odd arities n ≡ 1 (mod 4), the mathematical proof uses the
same six-vertex configuration with fixed 0/1 link signs alpha,beta.
The possible edges of the homogeneous-defect graph on these six
vertices are exactly 01,03,05,15,24,25,35.

The present module verifies this exact finite link table and isolates
the final combinatorial contradiction: a defect graph with degrees
zero or two, with a fixed external edge at a4 and none at a2, must
contain edges a2-a4 and a2-a5. Those two homogeneous packets force
opposite values of one common mixed facet.

This does not yet construct the full higher-arity hypertournament
or prove the geometric zero-or-two principle. Those are separate
formalization obligations; no AP statement is exported here.
-/

namespace Hypertournaments

/-- Core-pair locations at which the left link sign is zero.
The arguments are in increasing order. -/
def p1CoreLeftZero (i j : Fin 6) : Prop :=
  (i = 1 ∧ j = 4) ∨
  (i = 1 ∧ j = 5) ∨
  (i = 2 ∧ j = 4) ∨
  (i = 3 ∧ j = 4) ∨
  (i = 3 ∧ j = 5)

/-- Core-pair locations at which the right link sign is zero. -/
def p1CoreRightZero (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨
  (i = 0 ∧ j = 3) ∨
  (i = 0 ∧ j = 5) ∨
  (i = 1 ∧ j = 4) ∨
  (i = 2 ∧ j = 5) ∨
  (i = 3 ∧ j = 4)

def p1CoreLeftBit (i j : Fin 6) : Bool :=
  decide (¬ p1CoreLeftZero i j)

def p1CoreRightBit (i j : Fin 6) : Bool :=
  decide (¬ p1CoreRightZero i j)

/-- The seven allowed mixed edges on the six core vertices. -/
def p1CoreEligibleOrdered (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨
  (i = 0 ∧ j = 3) ∨
  (i = 0 ∧ j = 5) ∨
  (i = 1 ∧ j = 5) ∨
  (i = 2 ∧ j = 4) ∨
  (i = 2 ∧ j = 5) ∨
  (i = 3 ∧ j = 5)

/-- Symmetric version, independent of the order of the two endpoints. -/
def p1CoreEligible (i j : Fin 6) : Prop :=
  p1CoreEligibleOrdered (min i j) (max i j)

/-- Certified XOR support of the two explicitly prescribed core links. -/
theorem p1Core_eligible_iff_link_disagreement :
    ∀ i j : Fin 6, i < j →
      (p1CoreLeftBit i j ≠ p1CoreRightBit i j ↔
        p1CoreEligibleOrdered i j) := by
  decide

/-- Among core vertices, a4 only has the possible neighbor a2. -/
theorem p1Core_only_neighbor_four :
    ∀ j : Fin 6, p1CoreEligible 4 j ↔ j = 2 := by
  decide

/-- Among core vertices, a2 only has possible neighbors a4,a5. -/
theorem p1Core_only_neighbors_two :
    ∀ j : Fin 6, p1CoreEligible 2 j ↔ j = 4 ∨ j = 5 := by
  decide

/-- Number of core-core neighbors of a vertex in a Boolean graph. -/
def p1CoreDegree (e : Fin 6 → Fin 6 → Bool) (v : Fin 6) : ℕ :=
  (Finset.univ.filter (fun u => e v u = true)).card

/-- The zero-or-two degree restriction and the eligible-edge
support force the two crucial edges, independent of higher arity. -/
theorem p1Core_forced_edges
    (e : Fin 6 → Fin 6 → Bool)
    (hsym : ∀ i j, e i j = e j i)
    (hsupport : ∀ i j, e i j = true → p1CoreEligible i j)
    (hdegree4 :
      1 + p1CoreDegree e 4 = 0 ∨ 1 + p1CoreDegree e 4 = 2)
    (hdegree2 :
      p1CoreDegree e 2 = 0 ∨ p1CoreDegree e 2 = 2) :
    e 4 2 = true ∧ e 2 5 = true := by
  let N4 : Finset (Fin 6) :=
    Finset.univ.filter (fun u => e 4 u = true)
  have hsub4 : N4 ⊆ ({2} : Finset (Fin 6)) := by
    intro u hu
    have he : e 4 u = true := (Finset.mem_filter.mp hu).2
    have hEq : u = 2 :=
      (p1Core_only_neighbor_four u).mp (hsupport 4 u he)
    simp [hEq]
  have hdeg4le : p1CoreDegree e 4 ≤ 1 := by
    change N4.card ≤ 1
    calc
      N4.card ≤ ({2} : Finset (Fin 6)).card :=
        Finset.card_le_card hsub4
      _ = 1 := by simp
  have hdeg4pos : 0 < N4.card := by
    change 0 < p1CoreDegree e 4
    rcases hdegree4 with hz | ht <;> omega
  obtain ⟨u, hu⟩ := (Finset.card_pos.mp hdeg4pos)
  have hu2 : u = 2 := by
    simpa only [Finset.mem_singleton] using hsub4 hu
  have h42 : e 4 2 = true := by
    rw [← hu2]
    exact (Finset.mem_filter.mp hu).2
  have h24 : e 2 4 = true := by
    rw [hsym]
    exact h42
  have hdeg2pos : 0 < p1CoreDegree e 2 := by
    change 0 < (Finset.univ.filter (fun u => e 2 u = true)).card
    apply Finset.card_pos.mpr
    refine ⟨4, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, h24⟩
  have h25 : e 2 5 = true := by
    by_contra hfalse
    let N2 : Finset (Fin 6) :=
      Finset.univ.filter (fun u => e 2 u = true)
    have hsub2 : N2 ⊆ ({4} : Finset (Fin 6)) := by
      intro u hu
      have he : e 2 u = true := (Finset.mem_filter.mp hu).2
      have hpossible := (p1Core_only_neighbors_two u).mp
        (hsupport 2 u he)
      rcases hpossible with hu4 | hu5
      · simp [hu4]
      · subst u
        exact False.elim (hfalse he)
    have hdeg2le : p1CoreDegree e 2 ≤ 1 := by
      change N2.card ≤ 1
      calc
        N2.card ≤ ({4} : Finset (Fin 6)).card :=
          Finset.card_le_card hsub2
        _ = 1 := by simp
    rcases hdegree2 with hz | ht <;> omega
  exact ⟨h42, h25⟩

/-- The final forced-facet contradiction in the uniform p1 core:
the two forced homogeneous mixed packets read the same facet with
opposite prescribed signs. -/
theorem p1Core_forced_facet_contradiction
    (e : Fin 6 → Fin 6 → Bool) (sharedFacet : Bool)
    (hsym : ∀ i j, e i j = e j i)
    (hsupport : ∀ i j, e i j = true → p1CoreEligible i j)
    (hdegree4 :
      1 + p1CoreDegree e 4 = 0 ∨ 1 + p1CoreDegree e 4 = 2)
    (hdegree2 :
      p1CoreDegree e 2 = 0 ∨ p1CoreDegree e 2 = 2)
    (h24 : e 4 2 = true → sharedFacet = true)
    (h25 : e 2 5 = true → sharedFacet = false) :
    False := by
  obtain ⟨e42, e25⟩ :=
    p1Core_forced_edges e hsym hsupport hdegree4 hdegree2
  have htf : (true : Bool) = false :=
    (h24 e42).symm.trans (h25 e25)
  cases htf

end Hypertournaments
