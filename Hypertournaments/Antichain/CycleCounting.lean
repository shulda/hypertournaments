import Hypertournaments.Antichain.CycleQ
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Counting the four-vertex invariant in a cycle

This develops a degree-based version of Sullivan's Lemmas 4.9--4.10.
It avoids decomposing a proper induced subgraph into path components.
-/

open scoped BigOperators

namespace Hypertournaments.Antichain

def cyclePred {N : ℕ} (a : Fin N) : Fin N :=
  if h : a.val = 0 then ⟨N - 1, by have := a.isLt; omega⟩
  else ⟨a.val - 1, by have := a.isLt; omega⟩

def cycleSucc {N : ℕ} (a : Fin N) : Fin N :=
  if h : a.val + 1 = N then ⟨0, by have := a.isLt; omega⟩
  else ⟨a.val + 1, by have := a.isLt; omega⟩

theorem cycleAdj_iff_pred_succ {N : ℕ} (hN : 3 ≤ N) (a b : Fin N) :
    cycleAdj a b ↔ b = cyclePred a ∨ b = cycleSucc a := by
  have ha := a.isLt
  have hb := b.isLt
  unfold cyclePred cycleSucc cycleAdj
  split_ifs <;> simp only [Fin.ext_iff] <;> omega

theorem cyclePred_ne_cycleSucc {N : ℕ} (hN : 3 ≤ N) (a : Fin N) :
    cyclePred a ≠ cycleSucc a := by
  have ha := a.isLt
  unfold cyclePred cycleSucc
  split_ifs <;> simp only [ne_eq, Fin.ext_iff] <;> omega

@[simp] theorem cyclePred_cycleSucc {N : ℕ} (hN : 2 ≤ N) (a : Fin N) :
    cyclePred (cycleSucc a) = a := by
  have ha := a.isLt
  by_cases h : a.val + 1 = N
  · simp [cycleSucc, h, cyclePred, Fin.ext_iff]
    omega
  · simp [cycleSucc, h, cyclePred]

@[simp] theorem cycleSucc_cyclePred {N : ℕ} (hN : 2 ≤ N) (a : Fin N) :
    cycleSucc (cyclePred a) = a := by
  have ha := a.isLt
  by_cases h : a.val = 0
  · simp [cyclePred, h, cycleSucc, Fin.ext_iff, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  · have hlast : a.val - 1 + 1 ≠ N := by omega
    simp [cyclePred, h, cycleSucc, hlast, Fin.ext_iff]
    omega

def cycleNeighbors {N : ℕ} (V : Finset (Fin N)) (a : Fin N) : Finset (Fin N) :=
  V.filter (cycleAdj a)

@[simp] theorem mem_cycleNeighbors {N : ℕ} {V : Finset (Fin N)} {a b : Fin N} :
    b ∈ cycleNeighbors V a ↔ b ∈ V ∧ cycleAdj a b := by
  simp [cycleNeighbors]

theorem cycleNeighbors_eq_inter {N : ℕ} (hN : 3 ≤ N)
    (V : Finset (Fin N)) (a : Fin N) :
    cycleNeighbors V a = V ∩ {cyclePred a, cycleSucc a} := by
  ext b
  simp [cycleAdj_iff_pred_succ hN]

theorem cycleNeighbors_card_le {N : ℕ} (hN : 3 ≤ N)
    (V : Finset (Fin N)) (a : Fin N) : (cycleNeighbors V a).card ≤ 2 := by
  rw [cycleNeighbors_eq_inter hN]
  have hcard : ({cyclePred a, cycleSucc a} : Finset (Fin N)).card = 2 := by
    simp [cyclePred_ne_cycleSucc hN]
  simpa only [hcard] using (Finset.card_le_card
    (Finset.inter_subset_right : V ∩ {cyclePred a, cycleSucc a} ⊆ _))

theorem cycleNeighbors_univ_card {N : ℕ} (hN : 3 ≤ N) (a : Fin N) :
    (cycleNeighbors Finset.univ a).card = 2 := by
  simp [cycleNeighbors_eq_inter hN, cyclePred_ne_cycleSucc hN]

/-- Midpoints whose two cycle neighbours are present. -/
def cycleCenters {N : ℕ} (V : Finset (Fin N)) : Finset (Fin N) :=
  V.filter (fun a => cyclePred a ∈ V ∧ cycleSucc a ∈ V)

/-- Possible isolated vertices for the path with midpoint `a`. -/
def cycleFar {N : ℕ} (V : Finset (Fin N)) (a : Fin N) : Finset (Fin N) :=
  V.filter (fun x => x ≠ a ∧ ¬ cycleAdj a x ∧
    ¬ cycleAdj (cyclePred a) x ∧ ¬ cycleAdj (cycleSucc a) x)

/-- Each induced `Q` has one midpoint and one isolated vertex. -/
def cycleWitnesses {N : ℕ} (V : Finset (Fin N)) : Finset (Σ _ : Fin N, Fin N) :=
  (cycleCenters V).sigma (fun a => cycleFar V a)

def cycleWitnessCount {N : ℕ} (V : Finset (Fin N)) : ℕ := (cycleWitnesses V).card

def cycleQVertices {N : ℕ} (a x : Fin N) : Finset (Fin N) :=
  {cyclePred a, a, cycleSucc a, x}

@[simp] theorem mem_cycleCenters {N : ℕ} {V : Finset (Fin N)} {a : Fin N} :
    a ∈ cycleCenters V ↔ a ∈ V ∧ cyclePred a ∈ V ∧ cycleSucc a ∈ V := by
  simp [cycleCenters]

@[simp] theorem mem_cycleFar {N : ℕ} {V : Finset (Fin N)} {a x : Fin N} :
    x ∈ cycleFar V a ↔ x ∈ V ∧ x ≠ a ∧ ¬ cycleAdj a x ∧
      ¬ cycleAdj (cyclePred a) x ∧ ¬ cycleAdj (cycleSucc a) x := by
  simp [cycleFar]

@[simp] theorem mem_cycleWitnesses {N : ℕ} {V : Finset (Fin N)}
    {p : Σ _ : Fin N, Fin N} :
    p ∈ cycleWitnesses V ↔ p.1 ∈ cycleCenters V ∧ p.2 ∈ cycleFar V p.1 := by
  simp [cycleWitnesses]

theorem cyclePred_ne_self {N : ℕ} (hN : 2 ≤ N) (a : Fin N) : cyclePred a ≠ a := by
  have ha := a.isLt
  unfold cyclePred
  split_ifs <;> simp_all only [ne_eq, Fin.ext_iff] <;> omega

theorem cycleSucc_ne_self {N : ℕ} (hN : 2 ≤ N) (a : Fin N) : cycleSucc a ≠ a := by
  have ha := a.isLt
  unfold cycleSucc
  split_ifs <;> simp_all only [ne_eq, Fin.ext_iff] <;> omega

theorem cycleAdj_pred {N : ℕ} (hN : 3 ≤ N) (a : Fin N) : cycleAdj a (cyclePred a) :=
  (cycleAdj_iff_pred_succ hN _ _).mpr (Or.inl rfl)

theorem cycleAdj_succ {N : ℕ} (hN : 3 ≤ N) (a : Fin N) : cycleAdj a (cycleSucc a) :=
  (cycleAdj_iff_pred_succ hN _ _).mpr (Or.inr rfl)

theorem not_cycleAdj_pred_succ {N : ℕ} (hN : 4 ≤ N) (a : Fin N) :
    ¬ cycleAdj (cyclePred a) (cycleSucc a) := by
  have ha := a.isLt
  by_cases h0 : a.val = 0
  · have h1 : 1 ≠ N := by omega
    simp [cyclePred, cycleSucc, h0, h1, cycleAdj]
    omega
  · by_cases hl : a.val + 1 = N
    · simp [cyclePred, cycleSucc, h0, hl, cycleAdj]
      omega
    · simp [cyclePred, cycleSucc, h0, hl, cycleAdj]
      omega

end Hypertournaments.Antichain
