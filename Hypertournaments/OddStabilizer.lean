import Hypertournaments.Automorphism
import Hypertournaments.TwoPadIntrinsic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# Odd order of sufficiently large pointwise stabilizers

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
odd pointwise stabilizer lemma in the EPPA proof preparation.

An involution moving a vertex exchanges it with its image. Together with
`n-2` fixed vertices this produces an actual oriented n-tuple on which the
automorphism acts as a coordinate transposition, contradicting alternation.
Cauchy's theorem then gives odd order for the pointwise stabilizer.
-/

namespace Hypertournaments

universe u

/-- An intrinsic involution fixing an injective tuple of `n-2` vertices is
the identity. The carrier need not be finite. -/
theorem Hyper.Aut.eq_one_of_sq_eq_one_of_fixes_tuple
    {k : ℕ} {V : Type u} {A : Hyper (k + 2) V}
    (g : A.Aut) (hg : g * g = 1) (s : Fin k ↪ V)
    (hs : ∀ i, (g : Equiv.Perm V) (s i) = s i) : g = 1 := by
  classical
  by_contra hne
  have hex : ∃ x : V, (g : Equiv.Perm V) x ≠ x := by
    by_contra h
    apply hne
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  have hinv (y : V) : (g : Equiv.Perm V) ((g : Equiv.Perm V) y) = y := by
    exact congrArg (fun a : A.Aut => (a : Equiv.Perm V) y) hg
  have hp : x ∉ Set.range s := by
    rintro ⟨i, hi⟩
    exact hx (by simpa only [hi] using hs i)
  have hq : (g : Equiv.Perm V) x ∉ Set.range s := by
    rintro ⟨i, hi⟩
    have h := hs i
    rw [hi, hinv] at h
    exact hx h.symm
  let t : Fin (k + 2) ↪ V := twoPadTuple s x ((g : Equiv.Perm V) x) hp hq hx.symm
  have ht0 : t 0 = x := twoPadTuple_zero s x _ hp hq hx.symm
  have ht1 : t 1 = (g : Equiv.Perm V) x := twoPadTuple_one s x _ hp hq hx.symm
  have htold (i : Fin k) : t i.succ.succ = s i :=
    twoPadTuple_old s x _ hp hq hx.symm i
  have htuple : t.trans (g : Equiv.Perm V).toEmbedding =
      (Equiv.swap (0 : Fin (k + 2)) 1).toEmbedding.trans t := by
    ext i
    change (g : Equiv.Perm V) (t i) = t ((Equiv.swap (0 : Fin (k + 2)) 1) i)
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Equiv.swap_apply_left, ht0, ht1]
    · refine Fin.cases ?_ (fun j => ?_) i
      · change (g : Equiv.Perm V) (t 1) = t ((Equiv.swap (0 : Fin (k + 2)) 1) 1)
        rw [Equiv.swap_apply_right, ht1, hinv, ht0]
      · have h0 : j.succ.succ ≠ (0 : Fin (k + 2)) := by
          intro h
          have hh := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_zero] at hh
          omega
        have h1 : j.succ.succ ≠ (1 : Fin (k + 2)) := by
          intro h
          have hh := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_one] at hh
          omega
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1, htold, hs]
  have hpres := g.preserves t
  rw [htuple, A.swap_flip t 0 1 Fin.zero_ne_one] at hpres
  cases hbit : A.orient t <;> simp [hbit] at hpres

/-- The pointwise stabilizer of a set containing an injective `(n-2)`-tuple
has odd order, with no assumption that the other vertices exist. -/
theorem Hyper.odd_card_pointwiseStabilizer_of_tuple
    {k : ℕ} {V : Type u} [Finite V] (A : Hyper (k + 2) V)
    (S : Set V) (s : Fin k ↪ V) (hs : Set.range s ⊆ S) :
    Odd (Nat.card (A.pointwiseStabilizer S)) := by
  classical
  by_contra hodd
  have hdiv : 2 ∣ Nat.card (A.pointwiseStabilizer S) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := A.pointwiseStabilizer S) 2 hdiv
  have hsq : g * g = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hg, pow_two] at h
  have haut : (g : A.Aut) = 1 :=
    (g : A.Aut).eq_one_of_sq_eq_one_of_fixes_tuple
      (congrArg (fun a : A.pointwiseStabilizer S => (a : A.Aut)) hsq) s
      (fun i => (Hyper.mem_pointwiseStabilizer_iff.mp g.property) (s i) (hs ⟨i, rfl⟩))
  have heq : g = 1 := Subtype.ext haut
  rw [heq, orderOf_one] at hg
  omega

/-- For a finite n-hypertournament, the pointwise stabilizer of any set of
at least `n-2` vertices has odd order. This includes `n=2` and empty carriers. -/
theorem Hyper.odd_card_pointwiseStabilizer
    {n : ℕ} {V : Type u} [Finite V] (A : Hyper n V) (hn : 2 ≤ n)
    (S : Finset V) (hS : n - 2 ≤ S.card) :
    Odd (Nat.card (A.pointwiseStabilizer (S : Set V))) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hcard : Fintype.card (Fin k) ≤ S.card := by simpa using hS
  obtain ⟨s, hs⟩ := Function.Embedding.exists_of_card_le_finset hcard
  exact A.odd_card_pointwiseStabilizer_of_tuple (S : Set V) s hs

end Hypertournaments
