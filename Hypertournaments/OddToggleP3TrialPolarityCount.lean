import Hypertournaments.OddToggleP3BadTrialCount
import Hypertournaments.OddToggleP3MixedPolarity

/-!
# Exact Boolean mixed-packet event behind the p3 two-pattern count

The abstract two forbidden bit patterns were already counted exactly.
Here we identify that pattern condition with the actual *Boolean
endpoint/interior polarity test* used in a prospective mixed packet:
the m interior bits alternate, while the two endpoint contributions
are the same independent base bit XOR two distinct side-link bits.

The result is a deterministic exact event equivalence, followed by
its exact global finite frequency under an injective index map.
It is NOT yet a theorem identifying the canonical signs of an actual
hypothetical joint with these abstract input bits.
-/

namespace Hypertournaments

/-- Store the m mixed interior bits and the one independent W bit
in the same source-word representation used by the counting lemma. -/
def p3TrialPacketBits (m : ℕ) (interior : Fin m → Bool)
    (base : Bool) : (Fin m ⊕ Unit) → Bool
  | Sum.inl i => interior i
  | Sum.inr _ => base

/-- The exact endpoint/interior Boolean condition for a mixed packet
to be alternating: its interior is an alternating m-word, and
the endpoint signs (base XOR the two link contributions) are the
opposite endpoint bits required by that phase. -/
def p3TrialPolarity (m : ℕ) (left right : Bool)
    (interior : Fin m → Bool) (base : Bool) : Prop :=
  ∃ phase : Bool,
    (∀ i : Fin m, interior i = p3AlternatingWord m phase i) ∧
    ((base ^^ left) = phase) ∧ ((base ^^ right) = !phase)

/-- For opposite side-link contributions, the concrete Boolean
packet-polarity event equals membership in the two abstract forbidden
patterns, with bad-W choice phase XOR left. -/
theorem p3TrialPolarity_iff_badPatterns
    (m : ℕ) (left right : Bool) (hLR : left ≠ right)
    (interior : Fin m → Bool) (base : Bool) :
    p3TrialPolarity m left right interior base ↔
      p3TrialPacketBits m interior base ∈
        ((Finset.univ : Finset Bool).image
          (p3BadPattern m (fun phase => phase ^^ left))) := by
  classical
  constructor
  · rintro ⟨phase, hinner, hleft, _hright⟩
    apply Finset.mem_image.mpr
    refine ⟨phase, by simp, ?_⟩
    funext s
    cases s with
    | inl i =>
        change p3AlternatingWord m phase i = interior i
        exact (hinner i).symm
    | inr u =>
        cases u
        change (phase ^^ left) = base
        cases phase <;> cases left <;> cases base <;> simp_all
  · intro hmem
    obtain ⟨phase, _, hword⟩ := Finset.mem_image.mp hmem
    refine ⟨phase, ?_, ?_, ?_⟩
    · intro i
      have hi := congrFun hword (Sum.inl i)
      change p3AlternatingWord m phase i = interior i at hi
      exact hi.symm
    · have hb := congrFun hword (Sum.inr ())
      change (phase ^^ left) = base at hb
      cases phase <;> cases left <;> cases base <;> simp_all
    · have hb := congrFun hword (Sum.inr ())
      change (phase ^^ left) = base at hb
      cases phase <;> cases left <;> cases right <;>
        cases base <;> simp_all

/-- Under arbitrary finite independent source coordinates, exactly
a 2^(-m) fraction of assignments realize the full alternating
endpoint/interior Boolean event, not merely a renamed pattern
predicate. This is the finite integer identity (no probability
measure or ordinary AP theorem). -/
theorem p3TrialPolarity_exact_finite_frequency
    (m : ℕ) (hm : 0 < m)
    (left right : Bool) (hLR : left ≠ right)
    {B : Type*} [Fintype B]
    (f : (Fin m ⊕ Unit) → B) (hf : Function.Injective f) :
    2 ^ (m+1) *
      Nat.card {values : B → Bool //
        p3TrialPolarity m left right
          (fun i => values (f (Sum.inl i)))
          (values (f (Sum.inr ())))} =
    2 * 2 ^ (Fintype.card B) := by
  classical
  let P : Finset ((Fin m ⊕ Unit) → Bool) :=
    (Finset.univ : Finset Bool).image
      (p3BadPattern m (fun phase => phase ^^ left))
  let LeftEvent :=
    {values : B → Bool //
      p3TrialPolarity m left right
        (fun i => values (f (Sum.inl i)))
        (values (f (Sum.inr ())))}
  let RightEvent :=
    {values : B → Bool //
      (fun s : Fin m ⊕ Unit => values (f s)) ∈ P}
  have hEvent (values : B → Bool) :
      p3TrialPolarity m left right
        (fun i => values (f (Sum.inl i)))
        (values (f (Sum.inr ()))) ↔
      (fun s : Fin m ⊕ Unit => values (f s)) ∈ P := by
    have hbits :
        p3TrialPacketBits m
          (fun i => values (f (Sum.inl i)))
          (values (f (Sum.inr ()))) =
        (fun s : Fin m ⊕ Unit => values (f s)) := by
      funext s
      cases s with
      | inl i => rfl
      | inr u =>
          cases u
          rfl
    simpa only [P, hbits] using
      (p3TrialPolarity_iff_badPatterns
        m left right hLR
        (fun i => values (f (Sum.inl i)))
        (values (f (Sum.inr ()))))
  let e : LeftEvent ≃ RightEvent := {
    toFun := fun v => ⟨v.1, (hEvent v.1).mp v.2⟩
    invFun := fun v => ⟨v.1, (hEvent v.1).mpr v.2⟩
    left_inv := by intro v; cases v; rfl
    right_inv := by intro v; cases v; rfl
  }
  have hc : Nat.card LeftEvent = Nat.card RightEvent :=
    Nat.card_congr e
  have hbad :=
    p3BadTrial_exact_finite_frequency
      m hm f hf (fun phase => phase ^^ left)
  change 2 ^ (m+1) * Nat.card RightEvent =
    2 * 2 ^ (Fintype.card B) at hbad
  change 2 ^ (m+1) * Nat.card LeftEvent =
    2 * 2 ^ (Fintype.card B)
  rw [hc]
  exact hbad

end Hypertournaments
