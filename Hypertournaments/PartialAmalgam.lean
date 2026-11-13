import Lean.Elab.Tactic.Omega
import Hypertournaments.PartialHyper
import Hypertournaments.PairCancellation
import Hypertournaments.FiniteStrongSpan

/-!
# The partially prescribed union of two compatible hypertournaments

A tuple is prescribed precisely when it lies entirely in one side. The
missing pairs join the left-only points to the right-only points. This
module does not impose an order on the embeddings.
-/

universe u v w z

namespace Hypertournaments.PartialAmalgam

variable {n : ℕ} {A : Type u} {B : Type v} {C : Type w} {D : Type z}

def InRange (e : B ↪ D) (t : Fin n ↪ D) : Prop :=
  ∀ k, t k ∈ Set.range e

noncomputable def lift (e : B ↪ D) (t : Fin n ↪ D) (h : InRange e t) : Fin n ↪ B where
  toFun k := Classical.choose (h k)
  inj' := by
    intro k l hkl
    apply t.injective
    exact (Classical.choose_spec (h k)).symm.trans
      ((congrArg e hkl).trans (Classical.choose_spec (h l)))

@[simp] theorem lift_apply (e : B ↪ D) (t : Fin n ↪ D) (h : InRange e t) (k : Fin n) :
    e (lift e t h k) = t k :=
  Classical.choose_spec (h k)

@[simp] theorem lift_trans (e : B ↪ D) (t : Fin n ↪ D) (h : InRange e t) :
    (lift e t h).trans e = t := by
  ext k
  exact lift_apply e t h k

theorem inRange_trans (e : B ↪ D) (t : Fin n ↪ B) : InRange e (t.trans e) :=
  fun k => ⟨t k, rfl⟩

@[simp] theorem lift_source (e : B ↪ D) (t : Fin n ↪ B) (h : InRange e (t.trans e)) :
    lift e (t.trans e) h = t := by
  ext k
  apply e.injective
  exact lift_apply e (t.trans e) h k

theorem inRange_swap (e : B ↪ D) (t : Fin n ↪ D) (i j : Fin n) :
    InRange e ((Equiv.swap i j).toEmbedding.trans t) ↔ InRange e t := by
  constructor
  · intro h k
    have hh := h (Equiv.swap i j k)
    simpa using hh
  · intro h k
    exact h (Equiv.swap i j k)

theorem lift_swap (e : B ↪ D) (t : Fin n ↪ D) (i j : Fin n)
    (h : InRange e t) (hs : InRange e ((Equiv.swap i j).toEmbedding.trans t)) :
    lift e ((Equiv.swap i j).toEmbedding.trans t) hs =
      (Equiv.swap i j).toEmbedding.trans (lift e t h) := by
  ext k
  apply e.injective
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, lift_apply]

/-- On tuples contained in both sides, the prescribed values agree. -/
def Compatible (BB : Hyper n B) (CC : Hyper n C) (i : B ↪ D) (j : C ↪ D) : Prop :=
  ∀ b : Fin n ↪ B, ∀ c : Fin n ↪ C,
    b.trans i = c.trans j → BB.orient b = CC.orient c

theorem compatible_of_span (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (i : B ↪ D) (j : C ↪ D)
    (hB : Preserves AA BB f) (hC : Preserves AA CC g)
    (hoverlap : ∀ b c, i b = j c → ∃ a, f a = b ∧ g a = c) :
    Compatible BB CC i j := by
  classical
  intro b c hbc
  have ha : ∀ k, ∃ a, f a = b k ∧ g a = c k := by
    intro k
    exact hoverlap (b k) (c k) (congrArg (fun t : Fin n ↪ D => t k) hbc)
  let a : Fin n ↪ A := {
    toFun := fun k => Classical.choose (ha k)
    inj' := by
      intro k l hkl
      apply b.injective
      exact (Classical.choose_spec (ha k)).1.symm.trans
        ((congrArg f hkl).trans (Classical.choose_spec (ha l)).1) }
  have hf : a.trans f = b := by
    ext k
    exact (Classical.choose_spec (ha k)).1
  have hg : a.trans g = c := by
    ext k
    exact (Classical.choose_spec (ha k)).2
  calc
    BB.orient b = BB.orient (a.trans f) := congrArg BB.orient hf.symm
    _ = AA.orient a := hB a
    _ = CC.orient (a.trans g) := (hC a).symm
    _ = CC.orient c := congrArg CC.orient hg

/-- The free partial union; overlap compatibility is needed for preserving
both sides, but its alternating law holds independently of that hypothesis. -/
noncomputable def ofSides (BB : Hyper n B) (CC : Hyper n C) (i : B ↪ D) (j : C ↪ D) :
    PartialHyper n D := by
  classical
  exact {
    orient t := if hi : InRange i t then some (BB.orient (lift i t hi))
      else if hj : InRange j t then some (CC.orient (lift j t hj)) else none
    swap_flip := by
      intro t a b hab
      by_cases hi : InRange i t
      · have his := (inRange_swap i t a b).2 hi
        simp only [dite_eq_left hi, dite_eq_left his, lift_swap i t a b hi his,
          BB.swap_flip _ _ _ hab, Option.map_some]
      · have his : ¬ InRange i ((Equiv.swap a b).toEmbedding.trans t) :=
          fun hh => hi ((inRange_swap i t a b).1 hh)
        by_cases hj : InRange j t
        · have hjs := (inRange_swap j t a b).2 hj
          simp only [dite_eq_right hi, dite_eq_right his, dite_eq_left hj, dite_eq_left hjs,
            lift_swap j t a b hj hjs, CC.swap_flip _ _ _ hab, Option.map_some]
        · have hjs : ¬ InRange j ((Equiv.swap a b).toEmbedding.trans t) :=
            fun hh => hj ((inRange_swap j t a b).1 hh)
          simp only [dite_eq_right hi, dite_eq_right his, dite_eq_right hj, dite_eq_right hjs, Option.map_none]
  }

@[simp] theorem partial_left (BB : Hyper n B) (CC : Hyper n C)
    (i : B ↪ D) (j : C ↪ D) (t : Fin n ↪ B) :
    (ofSides BB CC i j).orient (t.trans i) = some (BB.orient t) := by
  have hi := inRange_trans i t
  simp only [ofSides, dite_eq_left hi, lift_source]

theorem partial_right (BB : Hyper n B) (CC : Hyper n C)
    (i : B ↪ D) (j : C ↪ D) (h : Compatible BB CC i j) (t : Fin n ↪ C) :
    (ofSides BB CC i j).orient (t.trans j) = some (CC.orient t) := by
  have hj := inRange_trans j t
  by_cases hi : InRange i (t.trans j)
  · simp only [ofSides, dite_eq_left hi]
    exact congrArg some (h (lift i (t.trans j) hi) t (lift_trans i (t.trans j) hi))
  · simp only [ofSides, dite_eq_right hi, dite_eq_left hj, lift_source]

theorem defined_iff (BB : Hyper n B) (CC : Hyper n C)
    (i : B ↪ D) (j : C ↪ D) (t : Fin n ↪ D) :
    (ofSides BB CC i j).orient t ≠ none ↔ InRange i t ∨ InRange j t := by
  classical
  by_cases hi : InRange i t <;> by_cases hj : InRange j t <;>
    simp [ofSides, hi, hj]

noncomputable def missing [Fintype D] (i : B ↪ D) (j : C ↪ D) : Finset (D × D) := by
  classical
  exact (Finset.univ.filter (fun x => x ∉ Set.range j)).product
    (Finset.univ.filter (fun x => x ∉ Set.range i))

@[simp] theorem mem_missing [Fintype D] (i : B ↪ D) (j : C ↪ D) (p : D × D) :
    p ∈ missing i j ↔ p.1 ∉ Set.range j ∧ p.2 ∉ Set.range i := by
  classical
  simp [missing]

theorem missing_ne [Fintype D] (i : B ↪ D) (j : C ↪ D)
    (hcover : ∀ d, d ∈ Set.range i ∨ d ∈ Set.range j)
    (p : D × D) (hp : p ∈ missing i j) : p.1 ≠ p.2 := by
  intro he
  obtain ⟨h1, h2⟩ := (mem_missing i j p).1 hp
  rcases hcover p.1 with h | h
  · exact h2 (he ▸ h)
  · exact h1 h

theorem cliqueDomain [Fintype D] [DecidableEq D]
    (BB : Hyper n B) (CC : Hyper n C) (i : B ↪ D) (j : C ↪ D) :
    (ofSides BB CC i j).HasCliqueDomain (missing i j) := by
  intro t
  rw [defined_iff]
  constructor
  · rintro (hi | hj) p hp ⟨h1, h2⟩
    · obtain ⟨k, hk⟩ := h2
      exact ((mem_missing i j p).1 hp).2 (hk ▸ hi k)
    · obtain ⟨k, hk⟩ := h1
      exact ((mem_missing i j p).1 hp).1 (hk ▸ hj k)
  · intro hfree
    by_cases hi : InRange i t
    · exact Or.inl hi
    right
    by_contra hj
    obtain ⟨k, hk⟩ := not_forall.1 hi
    obtain ⟨l, hl⟩ := not_forall.1 hj
    apply hfree (t l, t k) ((mem_missing i j _).2 ⟨hl, hk⟩)
    constructor
    · exact ⟨l, rfl⟩
    · exact ⟨k, rfl⟩

/-- A fully prescribed pair-cancelling copy in the free partial union lies
entirely on one side. The pair-link witness itself supplies a tuple containing
any proposed cross pair. -/
theorem prescribed_copy_inRange [Fintype D] [DecidableEq D]
    (P : PartialHyper n D) (i : B ↪ D) (j : C ↪ D)
    (hdom : P.HasCliqueDomain (missing i j))
    (hcover : ∀ d, d ∈ Set.range i ∨ d ∈ Set.range j)
    {m : ℕ} (F : Hyper n (Fin m)) (hF : PairCancelling F)
    (e : Fin m ↪ D)
    (hp : ∀ t : Fin n ↪ Fin m, P.orient (t.trans e) = some (F.orient t)) :
    InRange i e ∨ InRange j e := by
  classical
  by_cases hi : InRange i e
  · exact Or.inl hi
  right
  by_contra hj
  obtain ⟨v, hv⟩ := not_forall.1 hi
  obtain ⟨u, hu⟩ := not_forall.1 hj
  have huv : u ≠ v := by
    intro he
    subst v
    rcases hcover (e u) with h | h
    · exact hv h
    · exact hu h
  have hn : 3 ≤ n := hF.1
  obtain ⟨t, _, ht, _, _⟩ := hF.2.2 inferInstance u v huv
  have hdefined : P.orient (t.trans e) ≠ none := by rw [hp t]; simp
  apply (hdom (t.trans e)).1 hdefined (e u, e v) ((mem_missing i j _).2 ⟨hu, hv⟩)
  constructor
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.1 (ht.left_mem (by omega))
    exact ⟨k, congrArg e hk⟩
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.1 (ht.right_mem (by omega))
    exact ⟨k, congrArg e hk⟩

/-- The free partial union of two forbidden-free sides has no fully
prescribed forbidden copy, for a family of pair-cancelling structures. -/
theorem omits_of_pairCancelling [Fintype D] [DecidableEq D]
    (family : ForbiddenFamily n)
    (hpc : ∀ m (F : Hyper n (Fin m)), F ∈ family m → PairCancelling F)
    (BB : Hyper n B) (CC : Hyper n C) (i : B ↪ D) (j : C ↪ D)
    (hcompat : Compatible BB CC i j)
    (hcover : ∀ d, d ∈ Set.range i ∨ d ∈ Set.range j)
    (hB : Omits family BB) (hC : Omits family CC) :
    (ofSides BB CC i j).Omits family := by
  intro m F hF e hp
  rcases prescribed_copy_inRange (ofSides BB CC i j) i j
      (cliqueDomain BB CC i j) hcover F (hpc m F hF) e hp with hi | hj
  · apply hB m F hF (lift i e hi)
    intro t
    have he : (t.trans (lift i e hi)).trans i = t.trans e := by
      ext k
      exact lift_apply i e hi (t k)
    have hside := partial_left BB CC i j (t.trans (lift i e hi))
    rw [he] at hside
    exact Option.some.inj (hside.symm.trans (hp t))
  · apply hC m F hF (lift j e hj)
    intro t
    have he : (t.trans (lift j e hj)).trans j = t.trans e := by
      ext k
      exact lift_apply j e hj (t k)
    have hside := partial_right BB CC i j hcompat (t.trans (lift j e hj))
    rw [he] at hside
    exact Option.some.inj (hside.symm.trans (hp t))

/-- Complete input package for the same-carrier pair-cancelling completion
on the finite exact-overlap carrier of an arbitrary compatible span. -/
theorem exists_partial_span [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (family : ForbiddenFamily n)
    (hpc : ∀ m (F : Hyper n (Fin m)), F ∈ family m → PairCancelling F)
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Omits family BB) (hC : Omits family CC) :
    ∃ (P : PartialHyper n (FiniteStrongSpan.Carrier f g))
      (M : Finset (FiniteStrongSpan.Carrier f g × FiniteStrongSpan.Carrier f g)),
      (∀ p ∈ M, p.1 ≠ p.2) ∧ P.HasCliqueDomain M ∧ P.Omits family ∧
      (∀ t : Fin n ↪ B, P.orient (t.trans (FiniteStrongSpan.left f g)) = some (BB.orient t)) ∧
      (∀ t : Fin n ↪ C, P.orient (t.trans (FiniteStrongSpan.right f g)) = some (CC.orient t)) := by
  classical
  let i := FiniteStrongSpan.left f g
  let j := FiniteStrongSpan.right f g
  have hcover : ∀ d, d ∈ Set.range i ∨ d ∈ Set.range j := FiniteStrongSpan.covers f g
  have hcompat : Compatible BB CC i j := compatible_of_span AA BB CC f g i j hAB hAC
    (fun b c h => (FiniteStrongSpan.overlap f g b c).1 h)
  refine ⟨ofSides BB CC i j, missing i j, ?_, cliqueDomain BB CC i j,
    omits_of_pairCancelling family hpc BB CC i j hcompat hcover hB hC, ?_, ?_⟩
  · exact missing_ne i j hcover
  · exact partial_left BB CC i j
  · exact partial_right BB CC i j hcompat

end Hypertournaments.PartialAmalgam
