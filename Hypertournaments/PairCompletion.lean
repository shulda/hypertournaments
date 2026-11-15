import Hypertournaments.PairCancellation
import Hypertournaments.PartialHyper
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

/-!
# Direct same-carrier completion by the last missing pair

Source: `tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `prop:link-completion`.
This is the orientation part of that theorem. Conversion of arbitrary
relational inputs and their order relations is a subsequent adapter.

Pairs are stored as oriented representatives with distinct endpoints. Including
both representatives is harmless: an injective rank still selects one pair.
-/

namespace Hypertournaments
namespace PairCompletion

variable {V : Type*} [LinearOrder V]

def pairsIn (missing : Finset (V × V)) (X : Finset V) : Finset (V × V) :=
  missing.filter (fun p => p.1 ∈ X ∧ p.2 ∈ X)

noncomputable def lastPair (missing : Finset (V × V)) (rank : V × V → ℕ)
    (X : Finset V) (h : (pairsIn missing X).Nonempty) : V × V :=
  Classical.choose (Finset.exists_max_image (pairsIn missing X) rank h)

theorem lastPair_mem (missing : Finset (V × V)) (rank : V × V → ℕ)
    (X : Finset V) (h : (pairsIn missing X).Nonempty) :
    lastPair missing rank X h ∈ pairsIn missing X :=
  (Classical.choose_spec (Finset.exists_max_image (pairsIn missing X) rank h)).1

theorem lastPair_max (missing : Finset (V × V)) (rank : V × V → ℕ)
    (X : Finset V) (h : (pairsIn missing X).Nonempty)
    (p : V × V) (hp : p ∈ pairsIn missing X) :
    rank p ≤ rank (lastPair missing rank X h) :=
  (Classical.choose_spec (Finset.exists_max_image (pairsIn missing X) rank h)).2 p hp

theorem pairsIn_mono (missing : Finset (V × V)) {X Y : Finset V} (hXY : X ⊆ Y) :
    pairsIn missing X ⊆ pairsIn missing Y := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hm, ha, hb⟩
  exact Finset.mem_filter.mpr ⟨hm, hXY ha, hXY hb⟩

/-- The last missing pair of Y remains last in any subset containing it. -/
theorem lastPair_eq_of_subset
    (missing : Finset (V × V)) (rank : V × V → ℕ) (hrank : Function.Injective rank)
    {X Y : Finset V} (hXY : X ⊆ Y)
    (hX : (pairsIn missing X).Nonempty) (hY : (pairsIn missing Y).Nonempty)
    (hp : lastPair missing rank Y hY ∈ pairsIn missing X) :
    lastPair missing rank X hX = lastPair missing rank Y hY := by
  apply hrank
  apply Nat.le_antisymm
  · exact lastPair_max missing rank Y hY _
      (pairsIn_mono missing hXY (lastPair_mem missing rank X hX))
  · exact lastPair_max missing rank X hX _ hp

private theorem prescribed_of_no_pair {n : ℕ}
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdom : P.HasCliqueDomain missing) (f : Fin n ↪ V)
    (h : ¬ (pairsIn missing (tupleVertices f)).Nonempty) : P.orient f ≠ none := by
  apply (hdom f).2
  intro p hp he
  exact h ⟨p, Finset.mem_filter.mpr ⟨hp,
    (tupleVertices_mem_range f p.1).mpr he.1, (tupleVertices_mem_range f p.2).mpr he.2⟩⟩

/-- All undefined n-sets are filled independently by their last-pair template. -/
noncomputable def complete {n : ℕ}
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hdom : P.HasCliqueDomain missing) : Hyper n V where
  orient f :=
    if h : (pairsIn missing (tupleVertices f)).Nonempty then
      let p := lastPair missing rank (tupleVertices f) h
      (pairConstantTemplate (n := n) p.1 p.2
        (hdist p (Finset.mem_filter.mp (lastPair_mem missing rank _ h)).1)).orient f
    else (P.orient f).getD false
  swap_flip := by
    intro f i j hij
    simp only [tupleVertices_swap]
    by_cases h : (pairsIn missing (tupleVertices f)).Nonempty
    · simp only [dite_eq_left h]
      exact (pairConstantTemplate (n := n) _ _ _).swap_flip f i j hij
    · simp only [dite_eq_right h]
      have hknown := prescribed_of_no_pair P missing hdom f h
      cases he : P.orient f with
      | none => exact (hknown he).elim
      | some b => rw [P.swap_flip f i j hij, he]; rfl

theorem complete_orient_of_pair {n : ℕ}
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hdom : P.HasCliqueDomain missing) (f : Fin n ↪ V)
    (h : (pairsIn missing (tupleVertices f)).Nonempty) :
    (complete P missing hdist rank hdom).orient f =
      (pairConstantTemplate (n := n)
        (lastPair missing rank (tupleVertices f) h).1
        (lastPair missing rank (tupleVertices f) h).2
        (hdist _ (Finset.mem_filter.mp (lastPair_mem missing rank _ h)).1)).orient f := by
  simp only [complete, dite_eq_left h]

theorem complete_extends {n : ℕ}
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hdom : P.HasCliqueDomain missing) :
    P.Extends (complete P missing hdist rank hdom) := by
  intro f b hb
  have hnone : ¬ (pairsIn missing (tupleVertices f)).Nonempty := by
    rintro ⟨p, hp⟩
    rcases Finset.mem_filter.mp hp with ⟨hm, he⟩
    exact (hdom f).1 (by simp [hb]) p hm
      ⟨(tupleVertices_mem_range f p.1).mp he.1, (tupleVertices_mem_range f p.2).mp he.2⟩
  simp only [complete, dite_eq_right hnone, hb, Option.getD_some]

theorem complete_agrees_of_no_pair {n : ℕ}
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hdom : P.HasCliqueDomain missing) (f : Fin n ↪ V)
    (h : ¬ (pairsIn missing (tupleVertices f)).Nonempty) :
    P.orient f = some ((complete P missing hdist rank hdom).orient f) := by
  have hknown := prescribed_of_no_pair P missing hdom f h
  cases he : P.orient f with
  | none => exact (hknown he).elim
  | some b => rw [complete_extends P missing hdist rank hdom f b he]

theorem tupleVertices_trans_subset {n m : ℕ} (f : Fin n ↪ Fin m) (e : Fin m ↪ V) :
    tupleVertices (f.trans e) ⊆ tupleVertices e := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, rfl⟩

/-- Every link of the globally last missing pair is filled by the same template. -/
theorem complete_link {n : ℕ} (hn : 2 ≤ n)
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hrank : Function.Injective rank) (hdom : P.HasCliqueDomain missing)
    (Y : Finset V) (hY : (pairsIn missing Y).Nonempty)
    (f : Fin n ↪ V) (hf : tupleVertices f ⊆ Y)
    (hlink : IsPairLink (lastPair missing rank Y hY).1
      (lastPair missing rank Y hY).2 f) :
    (complete P missing hdist rank hdom).orient f = false := by
  have hp : lastPair missing rank Y hY ∈ pairsIn missing (tupleVertices f) := by
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (lastPair_mem missing rank Y hY)).1,
        hlink.left_mem hn, hlink.right_mem hn⟩
  have hX : (pairsIn missing (tupleVertices f)).Nonempty := ⟨_, hp⟩
  rw [complete_orient_of_pair P missing hdist rank hdom f hX]
  have heq := lastPair_eq_of_subset missing rank hrank hf hX hY hp
  simp only [heq]
  exact pairConstantTemplate_orient _ hn f hlink

/-- No pair-cancelling forbidden structure is introduced by the completion. -/
theorem complete_omits {n : ℕ} (hn : 2 ≤ n)
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (rank : V × V → ℕ)
    (hrank : Function.Injective rank) (hdom : P.HasCliqueDomain missing)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    (hP : P.Omits family) : Omits family (complete P missing hdist rank hdom) := by
  intro m F hF e he
  let Y := tupleVertices e
  by_cases hY : (pairsIn missing Y).Nonempty
  · let p := lastPair missing rank Y hY
    have hp := Finset.mem_filter.mp (lastPair_mem missing rank Y hY)
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hp.2.1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hp.2.2
    have hab : a ≠ b := by
      intro h
      apply hdist p hp.1
      exact ha.symm.trans ((congrArg e h).trans hb)
    let order : LinearOrder (Fin m) := LinearOrder.lift' e e.injective
    obtain ⟨s, t, hs, ht, hst⟩ := (hpc m F hF).2.2 order a b hab
    have maplink : ∀ (f : Fin n ↪ Fin m),
        @IsPairLink n (Fin m) order a b f → IsPairLink p.1 p.2 (f.trans e) := by
      intro f h
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        exact (congrArg e (h.1 i hi)).trans ha
      · intro i hi
        exact (congrArg e (h.2.1 i hi)).trans hb
      · intro i j hi hij
        exact h.2.2 i j hi hij
    have hs0 := complete_link hn P missing hdist rank hrank hdom Y hY
      (s.trans e) (tupleVertices_trans_subset s e) (maplink s hs)
    have ht0 := complete_link hn P missing hdist rank hrank hdom Y hY
      (t.trans e) (tupleVertices_trans_subset t e) (maplink t ht)
    exact hst ((he s).symm.trans (hs0.trans (ht0.symm.trans (he t))))
  · apply hP m F hF e
    intro f
    have hX : ¬ (pairsIn missing (tupleVertices (f.trans e))).Nonempty := by
      rintro ⟨p, hp⟩
      exact hY ⟨p, pairsIn_mono missing (tupleVertices_trans_subset f e) hp⟩
    simpa only [he f] using complete_agrees_of_no_pair P missing hdist rank hdom (f.trans e) hX

end PairCompletion

/-- Finite same-carrier completion, with no rank or completion provider assumed. -/
theorem exists_pair_cancelling_completion {n : ℕ} (hn : 2 ≤ n)
    {V : Type*} [LinearOrder V] [Finite V]
    (P : PartialHyper n V) (missing : Finset (V × V))
    (hdist : ∀ p ∈ missing, p.1 ≠ p.2) (hdom : P.HasCliqueDomain missing)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    (hP : P.Omits family) :
    ∃ D : Hyper n V, P.Extends D ∧ Omits family D := by
  classical
  let : Fintype (V × V) := Fintype.ofFinite _
  let rank : V × V → ℕ := fun p => (Fintype.equivFin (V × V) p).val
  have hrank : Function.Injective rank :=
    Fin.val_injective.comp (Fintype.equivFin (V × V)).injective
  exact ⟨PairCompletion.complete P missing hdist rank hdom,
    PairCompletion.complete_extends P missing hdist rank hdom,
    PairCompletion.complete_omits hn P missing hdist rank hrank hdom family hpc hP⟩

end Hypertournaments
