import Hypertournaments.OnePointJoint
import Hypertournaments.PartialHyper
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Ordinary and strong amalgamation for finite hypertournament classes

The membership predicate is arbitrary: in particular it can impose conditions
in several local cardinalities at once. All embeddings are the original
intrinsic orientation-preserving injections. The old local-palette `HasAP`
definition is unchanged and is a definitional instance of this interface.
-/

namespace Hypertournaments

/-- A class of finite intrinsic hypertournaments, using `Fin` presentations. -/
abbrev FiniteClass (n : ℕ) := ∀ m : ℕ, Hyper n (Fin m) → Prop

namespace FiniteClass

variable {n : ℕ}

/-- Membership is retained by induced substructures along arbitrary injections. -/
def Hereditary (K : FiniteClass n) : Prop :=
  ∀ ⦃a b : ℕ⦄ (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (e : Fin a ↪ Fin b),
    Preserves A B e → K b B → K a A

/-- Ordinary AP permits identifications outside the base. -/
def HasAP (K : FiniteClass n) : Prop :=
  ∀ (a b c : ℕ) (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c)),
    K a A → K b B → K c C →
    ∀ (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c), Preserves A B f → Preserves A C g →
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
      K d D ∧ Preserves B D i ∧ Preserves C D j ∧
        (∀ x, i (f x) = j (g x))

/-- Strong AP additionally requires exact overlap of the two embedded sides. -/
def HasSAP (K : FiniteClass n) : Prop :=
  ∀ (a b c : ℕ) (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c)),
    K a A → K b B → K c C →
    ∀ (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c), Preserves A B f → Preserves A C g →
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
      K d D ∧ Preserves B D i ∧ Preserves C D j ∧
        (∀ x, i (f x) = j (g x)) ∧
        (∀ y z, i y = j z → ∃ x, f x = y ∧ g x = z)

/-- Joint embedding uses actual embeddings of both given structures. -/
def HasJEP (K : FiniteClass n) : Prop :=
  ∀ (a b : ℕ) (A : Hyper n (Fin a)) (B : Hyper n (Fin b)), K a A → K b B →
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (i : Fin a ↪ Fin d) (j : Fin b ↪ Fin d),
      K d D ∧ Preserves A D i ∧ Preserves B D j

/-- Arbitrarily large finite members. -/
def Unbounded (K : FiniteClass n) : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ A : Hyper n (Fin m), K m A

theorem Hereditary.pullback {K : FiniteClass n} (hK : K.Hereditary)
    {a b : ℕ} (B : Hyper n (Fin b)) (e : Fin a ↪ Fin b) (hB : K b B) :
    K a (B.pullback e) :=
  hK (B.pullback e) B e (fun _ => rfl) hB

theorem HasSAP.hasAP {K : FiniteClass n} (h : K.HasSAP) : K.HasAP := by
  intro a b c A B C hA hB hC f g hf hg
  obtain ⟨d, D, i, j, hD, hi, hj, hc, _⟩ := h a b c A B C hA hB hC f g hf hg
  exact ⟨d, D, i, j, hD, hi, hj, hc⟩

/-- Class equality is transported at the actual finite AP quantifiers. -/
theorem hasAP_congr {K L : FiniteClass n}
    (h : ∀ m A, K m A ↔ L m A) : K.HasAP ↔ L.HasAP := by
  constructor
  · intro hAP a b c A B C hA hB hC f g hf hg
    obtain ⟨d, D, i, j, hD, hi, hj, hc⟩ := hAP a b c A B C
      ((h a A).mpr hA) ((h b B).mpr hB) ((h c C).mpr hC) f g hf hg
    exact ⟨d, D, i, j, (h d D).mp hD, hi, hj, hc⟩
  · intro hAP a b c A B C hA hB hC f g hf hg
    obtain ⟨d, D, i, j, hD, hi, hj, hc⟩ := hAP a b c A B C
      ((h a A).mp hA) ((h b B).mp hB) ((h c C).mp hC) f g hf hg
    exact ⟨d, D, i, j, (h d D).mpr hD, hi, hj, hc⟩

theorem hasSAP_congr {K L : FiniteClass n}
    (h : ∀ m A, K m A ↔ L m A) : K.HasSAP ↔ L.HasSAP := by
  constructor
  · intro hAP a b c A B C hA hB hC f g hf hg
    obtain ⟨d, D, i, j, hD, hi, hj, hc, ho⟩ := hAP a b c A B C
      ((h a A).mpr hA) ((h b B).mpr hB) ((h c C).mpr hC) f g hf hg
    exact ⟨d, D, i, j, (h d D).mp hD, hi, hj, hc, ho⟩
  · intro hAP a b c A B C hA hB hC f g hf hg
    obtain ⟨d, D, i, j, hD, hi, hj, hc, ho⟩ := hAP a b c A B C
      ((h a A).mp hA) ((h b B).mp hB) ((h c C).mp hC) f g hf hg
    exact ⟨d, D, i, j, (h d D).mpr hD, hi, hj, hc, ho⟩

/-- In positive arity the empty structure is unique, so hereditary AP gives JEP.
The positive-arity hypothesis is necessary: nullary orientations may differ. -/
theorem HasAP.hasJEP {K : FiniteClass n} (hAP : K.HasAP)
    (hK : K.Hereditary) (hn : 0 < n) : K.HasJEP := by
  intro a b A B hA hB
  let eA : Fin 0 ↪ Fin a := Function.Embedding.ofIsEmpty
  let eB : Fin 0 ↪ Fin b := Function.Embedding.ofIsEmpty
  let E := A.pullback eA
  have hE : K 0 E := hK.pullback A eA hA
  have hEA : Preserves E A eA := fun _ => rfl
  have hEB : Preserves E B eB := by
    intro t
    exact Fin.elim0 (t ⟨0, hn⟩)
  obtain ⟨d, D, i, j, hD, hi, hj, _⟩ :=
    hAP 0 a b E A B hE hA hB eA eB hEA hEB
  exact ⟨d, D, i, j, hD, hi, hj⟩

/-- JEP and unboundedness place any given member in arbitrarily large members. -/
theorem HasJEP.exists_large_extension {K : FiniteClass n}
    (hJ : K.HasJEP) (hU : K.Unbounded) {a : ℕ}
    (A : Hyper n (Fin a)) (hA : K a A) (N : ℕ) :
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (e : Fin a ↪ Fin d),
      N ≤ d ∧ K d D ∧ Preserves A D e := by
  obtain ⟨b, hb, B, hB⟩ := hU N
  obtain ⟨d, D, i, j, hD, hi, _hj⟩ := hJ a b A B hA hB
  have hbd : b ≤ d := by simpa using Fintype.card_le_of_injective j j.injective
  exact ⟨d, D, i, hb.trans hbd, hD, hi⟩

/-- Every member of an unbounded hereditary JEP class has a genuine one-point
extension. In particular, allowed small structures cannot be isolated artefacts
of constraints that are vacuous on their own carrier. -/
theorem HasJEP.exists_onePoint_extension {K : FiniteClass n}
    (hJ : K.HasJEP) (hK : K.Hereditary) (hU : K.Unbounded) {a : ℕ}
    (A : Hyper n (Fin a)) (hA : K a A) :
    ∃ B : Hyper n (Fin (a + 1)), K (a + 1) B ∧
      Preserves A B (onePointBaseEmbedding a) := by
  classical
  obtain ⟨d, D, i, hd, hD, hi⟩ := hJ.exists_large_extension hU A hA (a + 1)
  have hout : ∃ p : Fin d, p ∉ Set.range i := by
    by_contra! h
    have hcard : d ≤ a := by
      simpa using Fintype.card_le_of_surjective (i : Fin a → Fin d) h
    omega
  obtain ⟨p, hp⟩ := hout
  let e : Fin (a + 1) ↪ Fin d := Fin.Embedding.snoc i hp
  let B := D.pullback e
  refine ⟨B, hK.pullback D e hD, ?_⟩
  intro t
  have ht : (t.trans (onePointBaseEmbedding a)).trans e = t.trans i := by
    ext x
    exact congrArg Fin.val (Fin.Embedding.snoc_castSucc (x := i) (ha := hp))
  change D.orient ((t.trans (onePointBaseEmbedding a)).trans e) = _
  rw [ht]
  exact hi t

/-- An admitted member with no one-point extension rules out JEP in every
unbounded hereditary class. -/
theorem not_hasJEP_of_no_onePoint_extension {K : FiniteClass n}
    (hK : K.Hereditary) (hU : K.Unbounded) {a : ℕ}
    (A : Hyper n (Fin a)) (hA : K a A)
    (hno : ∀ B : Hyper n (Fin (a + 1)), K (a + 1) B →
      ¬ Preserves A B (onePointBaseEmbedding a)) : ¬ K.HasJEP := by
  intro hJ
  obtain ⟨B, hB, hAB⟩ := hJ.exists_onePoint_extension hK hU A hA
  exact hno B hB hAB

/-- A terminal admitted member disproves ordinary AP; identifying vertices
cannot repair the resulting joint-embedding obstruction. -/
theorem not_hasAP_of_no_onePoint_extension {K : FiniteClass n}
    (hK : K.Hereditary) (hU : K.Unbounded) (hn : 0 < n) {a : ℕ}
    (A : Hyper n (Fin a)) (hA : K a A)
    (hno : ∀ B : Hyper n (Fin (a + 1)), K (a + 1) B →
      ¬ Preserves A B (onePointBaseEmbedding a)) : ¬ K.HasAP := by
  intro hAP
  exact not_hasJEP_of_no_onePoint_extension hK hU A hA hno (hAP.hasJEP hK hn)

/-- For an arbitrary hereditary class, a bad canonical one-point union with
different sides already excludes ordinary AP, including all identifications. -/
theorem not_hasAP_of_no_joint {K : FiniteClass n} (hK : K.Hereditary)
    {a : ℕ} (A : Hyper n (Fin a)) (L R : Hyper n (Fin (a + 1)))
    (hA : K a A) (hL : K (a + 1) L) (hR : K (a + 1) R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hdisagree : ∃ t : Fin n ↪ Fin (a + 1), L.orient t ≠ R.orient t)
    (hNoJoint : ∀ E : Hyper n (Fin (a + 2)), K (a + 2) E →
      Preserves L E (leftJointInclusion a) →
      Preserves R E (rightJointInclusion a) → False) : ¬ K.HasAP := by
  intro hAP
  obtain ⟨d, D, i, j, hD, hi, hj, hbase⟩ :=
    hAP a (a + 1) (a + 1) A L R hA hL hR
      (onePointBaseEmbedding a) (onePointBaseEmbedding a) hAL hAR
  have hbase' : ∀ x : Fin a, i x.castSucc = j x.castSucc := hbase
  have hdistinct := onePoint_points_distinct_of_orient_disagree L R D i j
    hbase' hi hj hdisagree
  obtain ⟨e, hleft, hright⟩ := exists_joint_embedding a d i j hbase' hdistinct
  let E := D.pullback e
  have hE : K (a + 2) E := hK.pullback D e hD
  have hEL : Preserves L E (leftJointInclusion a) := by
    intro t
    have ht : (t.trans (leftJointInclusion a)).trans e = t.trans i := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hleft (t x))
    change D.orient ((t.trans (leftJointInclusion a)).trans e) = _
    rw [ht]
    exact hi t
  have hER : Preserves R E (rightJointInclusion a) := by
    intro t
    have ht : (t.trans (rightJointInclusion a)).trans e = t.trans j := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hright (t x))
    change D.orient ((t.trans (rightJointInclusion a)).trans e) = _
    rw [ht]
    exact hj t
  exact hNoJoint E hE hEL hER

/-- The arbitrary-class AP interface specializes definitionally to the original
ordinary local-palette AP interface. -/
theorem hasAP_admissible_iff (S : Set ℕ) :
    HasAP (fun m (A : Hyper n (Fin m)) => Admissible S A) ↔
      Hypertournaments.HasAP n S := Iff.rfl

/-- The omission-class strong AP interface is precisely the previously defined
strong amalgamation property, including its exact-overlap conclusion. -/
theorem hasSAP_omits_iff (family : ForbiddenFamily n) :
    HasSAP (fun m (A : Hyper n (Fin m)) => Omits family A) ↔
      HasStrongAmalgamation family := Iff.rfl

theorem hereditary_omits (family : ForbiddenFamily n) :
    Hereditary (fun m (A : Hyper n (Fin m)) => Omits family A) := by
  intro a b A B e hAB hB m F hF f hp
  apply hB m F hF (f.trans e)
  intro t
  exact (hAB (t.trans f)).trans (hp t)

end FiniteClass
end Hypertournaments
