import Hypertournaments.Basic

/-!
# The induced relational encoding of an orientation

The paper uses truth of R for orientation zero (`false`). Repeated coordinates
never satisfy R. This adapter does not impose an auxiliary vertex order and
expresses reflection as well as preservation of the relation.
-/

namespace Hypertournaments

/-- The single n-ary relation associated with an intrinsic hypertournament. -/
def Hyper.Relation {n : ℕ} {V : Type*} (A : Hyper n V) (t : Fin n → V) : Prop :=
  ∃ h : Function.Injective t, A.orient ⟨t, h⟩ = false

@[simp]
theorem Hyper.relation_embedding {n : ℕ} {V : Type*}
    (A : Hyper n V) (t : Fin n ↪ V) :
    A.Relation t ↔ A.orient t = false := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨t.injective, h⟩

theorem Hyper.not_relation_of_not_injective {n : ℕ} {V : Type*}
    (A : Hyper n V) (t : Fin n → V) (h : ¬ Function.Injective t) :
    ¬ A.Relation t := fun ht => h ht.1

/-- A vertex injection preserves orientations iff it is an induced embedding
for the relational encoding, including all tuples with repeated coordinates. -/
theorem preserves_iff_relation {n : ℕ} {V W : Type*}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) :
    Preserves A B e ↔ ∀ t : Fin n → V, B.Relation (e ∘ t) ↔ A.Relation t := by
  constructor
  · intro h t
    constructor
    · rintro ⟨ht, hb⟩
      have hinj : Function.Injective t := fun _ _ hxy => ht (congrArg e hxy)
      refine ⟨hinj, ?_⟩
      have he := h ⟨t, hinj⟩
      exact he.symm.trans hb
    · rintro ⟨ht, ha⟩
      refine ⟨e.injective.comp ht, ?_⟩
      exact (h ⟨t, ht⟩).trans ha
  · intro h t
    have hrel : B.orient (t.trans e) = false ↔ A.orient t = false := by
      have hh := h (t : Fin n → V)
      change B.Relation (t.trans e) ↔ A.Relation t at hh
      simpa only [Hyper.relation_embedding] using hh
    cases hb : B.orient (t.trans e) <;> cases ha : A.orient t <;> simp_all

@[simp]
theorem Hyper.relation_pullback {n : ℕ} {V W : Type*}
    (B : Hyper n W) (e : V ↪ W) (t : Fin n → V) :
    (B.pullback e).Relation t ↔ B.Relation (e ∘ t) := by
  exact ((preserves_iff_relation (B.pullback e) B e).mp (fun _ => rfl) t).symm

end Hypertournaments
