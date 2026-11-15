import Hypertournaments.Antichain.CycleTournament
import Mathlib.Data.Finset.Powerset

/-! The order-free four-vertex invariant used to distinguish the cycles. -/

namespace Hypertournaments.Antichain

/-- A path on three vertices and an isolated fourth vertex, in a specified
enumeration. Vertex `1` is the midpoint and vertex `3` is isolated. -/
def cycleQFrame {N : ℕ} (f : Fin 4 ↪ Fin N) : Prop :=
  cycleAdj (f 0) (f 1) ∧ cycleAdj (f 1) (f 2) ∧
    ¬ cycleAdj (f 0) (f 2) ∧ ¬ cycleAdj (f 0) (f 3) ∧
    ¬ cycleAdj (f 1) (f 3) ∧ ¬ cycleAdj (f 2) (f 3)

/-- An unlabelled induced copy of `P₃ ⊔ K₁` in the cycle. -/
def cycleQ {N : ℕ} (s : Finset (Fin N)) : Prop :=
  ∃ f : Fin 4 ↪ Fin N, s = {f 0, f 1, f 2, f 3} ∧ cycleQFrame f

noncomputable instance {N : ℕ} (s : Finset (Fin N)) : Decidable (cycleQ s) :=
  Classical.propDecidable _

/-- The unlabelled copies contained in a given set of cycle vertices. -/
noncomputable def cycleQCopies {N : ℕ} (V : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (V.powersetCard 4).filter cycleQ

/-- Number of induced copies, rather than number of labelled embeddings. -/
noncomputable def cycleQCount {N : ℕ} (V : Finset (Fin N)) : ℕ :=
  (cycleQCopies V).card

@[simp] theorem mem_cycleQCopies {N : ℕ} {V s : Finset (Fin N)} :
    s ∈ cycleQCopies V ↔ s ⊆ V ∧ s.card = 4 ∧ cycleQ s := by
  simp [cycleQCopies, Finset.mem_powersetCard, and_assoc]

end Hypertournaments.Antichain
