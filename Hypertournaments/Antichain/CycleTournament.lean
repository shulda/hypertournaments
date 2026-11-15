import Hypertournaments.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Cycle-twisted tournaments

Sullivan, `Ultrahomogeneous hypertournaments`, arXiv:2611.07292v1,
Definition 4.1. The graph consists of consecutive edges of `Fin N`, together
with its closing edge. Reversing these edges in the transitive tournament
gives the finite tournaments used in the antichain construction.
-/

namespace Hypertournaments.Antichain

/-- Adjacency in the undirected cycle on `Fin N`. -/
def cycleAdj {N : ℕ} (a b : Fin N) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
    (a.val = 0 ∧ b.val + 1 = N) ∨ (b.val = 0 ∧ a.val + 1 = N)

instance {N : ℕ} : DecidableRel (@cycleAdj N) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem cycleAdj_symm {N : ℕ} (a b : Fin N) : cycleAdj a b ↔ cycleAdj b a := by
  unfold cycleAdj
  tauto

theorem cycleAdj_irrefl {N : ℕ} (hN : 2 ≤ N) (a : Fin N) : ¬ cycleAdj a a := by
  simp only [cycleAdj]
  omega

theorem cycleAdj_of_consecutive {N : ℕ} {a b : Fin N}
    (h : a.val + 1 = b.val) : cycleAdj a b := Or.inl h

theorem cycleAdj_iff_of_lt {N : ℕ} {a b : Fin N} (hab : a < b) :
    cycleAdj a b ↔ a.val + 1 = b.val ∨ (a.val = 0 ∧ b.val + 1 = N) := by
  simp only [cycleAdj]
  have ha := a.isLt
  have hb := b.isLt
  change a.val < b.val at hab
  omega

/-- Direction bit of the transitive tournament with cycle edges reversed. -/
def cycleTournamentBit {N : ℕ} (a b : Fin N) : Bool :=
  decide (b < a) ^^ decide (cycleAdj a b)

theorem cycleTournamentBit_swap {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    cycleTournamentBit b a = !(cycleTournamentBit a b) := by
  have hadj := cycleAdj_symm a b
  unfold cycleTournamentBit
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : ¬ b < a := not_lt_of_ge (le_of_lt h)
    simp only [h, h', decide_true, decide_false, Bool.true_xor, Bool.false_xor]
    simp only [hadj]
  · have h' : ¬ a < b := not_lt_of_ge (le_of_lt h)
    simp only [h, h', decide_true, decide_false, Bool.true_xor, Bool.false_xor]
    simp only [hadj, Bool.not_not]

/-- The actual tournament, with the shared intrinsic `Hyper` encoding. -/
def cycleTournament (N : ℕ) : Hyper 2 (Fin N) where
  orient f := cycleTournamentBit (f 0) (f 1)
  swap_flip := by
    intro f i j hij
    have h01 : f 0 ≠ f 1 := fun h => by
      have := f.injective h
      exact (by decide : (0 : Fin 2) ≠ 1) this
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa using cycleTournamentBit_swap h01
    · simpa using cycleTournamentBit_swap h01
    · exact (hij rfl).elim

@[simp] theorem cycleTournament_orient (N : ℕ) (f : Fin 2 ↪ Fin N) :
    (cycleTournament N).orient f = cycleTournamentBit (f 0) (f 1) := rfl

end Hypertournaments.Antichain
