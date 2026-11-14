import Hypertournaments.FiveConstrained.CatalogueAction

namespace Hypertournaments.FiveConstrained

theorem relabel5_one (m : Fin 1024) : relabel5 m.val 1 = m.val := by
  calc
    relabel5 m.val 1 = encode5 (maskHyper 5 m.val) := by
      apply encode5_congr
      intro t
      rfl
    _ = m.val := encode5_maskHyper m

/-- The executable orbit label is invariant under every actual vertex permutation. -/
theorem type5_relabel5 (m : Fin 1024) (σ : Equiv.Perm (Fin 5)) :
    type5 (relabel5 m.val σ) = type5 m.val := by
  let M : Submonoid (Equiv.Perm (Fin 5)) := {
    carrier := {σ | ∀ m : Fin 1024, type5 (relabel5 m.val σ) = type5 m.val}
    one_mem' := by intro m; rw [relabel5_one]
    mul_mem' := by
      intro σ τ hσ hτ m
      rw [← relabel5_mul]
      exact (hτ ⟨relabel5 m.val σ, relabel5_lt _ _⟩).trans (hσ m)
  }
  have hclosure : Submonoid.closure
      (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) ≤ M := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩ n
    exact type5_relabel5_adjacent n i
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hclosure
  exact hclosure (show σ ∈ (⊤ : Submonoid (Equiv.Perm (Fin 5))) from trivial) m

/-- Orientation-preserving bijections preserve the computed five-type. -/
theorem type5_encode5_preserves (A B : Hyper 3 (Fin 5))
    (σ : Equiv.Perm (Fin 5)) (hp : Preserves A B σ.toEmbedding) :
    type5 (encode5 A) = type5 (encode5 B) := by
  have hr : relabel5 (encode5 B) σ = encode5 A := by
    apply encode5_congr
    intro t
    change (maskHyper 5 (encode5 B)).orient (t.trans σ.toEmbedding) = _
    rw [maskHyper_encode5]
    exact hp t
  rw [← hr]
  exact type5_relabel5 ⟨encode5 B, encode5_lt B⟩ σ

end Hypertournaments.FiveConstrained
