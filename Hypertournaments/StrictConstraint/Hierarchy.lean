import Hypertournaments.StrictConstraint.Classes
import Hypertournaments.StrictConstraint.CoverLink
import Hypertournaments.StrictConstraint.Extension
import Hypertournaments.LocalTypeRealization

/-!
# A strict hierarchy of local constraints

Source: `tex_hypertournaments`, commit
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`obs:strict-constrained-hierarchy`.

The construction starts with the homogeneous `(n+1)`-packet and adds one
vertex at a time with a homogeneous covering link. Thus every size `k > n`
is realized; no lower bound from the separate cycle antichain is needed.
-/

namespace Hypertournaments

theorem exists_pairCancelling_every_size {n k : ℕ} (hn : 3 ≤ n) (hk : n < k) :
    ∃ F : Hyper n (Fin k), PairCancelling F := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hbase : ∃ F : Hyper (r + 1) (Fin (r + 1 + 1)), PairCancelling F := by
    refine ⟨localTypeRepresentative (r + 1) 0, pairCancelling_of_localIndex_le hn _ ?_⟩
    rw [localIndex_localTypeRepresentative _ _ (Nat.zero_le _)]
    exact Nat.zero_le _
  have hstep (m : ℕ) (hm : r + 1 + 1 ≤ m)
      (ih : ∃ F : Hyper (r + 1) (Fin m), PairCancelling F) :
      ∃ F : Hyper (r + 1) (Fin (m + 1)), PairCancelling F := by
    obtain ⟨A, hA⟩ := ih
    obtain ⟨L, hL⟩ := StrictConstraint.exists_homogeneous_cover_link (by omega : r + 1 ≤ m)
    obtain ⟨E, _hold, hE⟩ :=
      StrictConstraint.exists_pairCancelling_extension (by omega : 2 ≤ r) A hA L hL
    exact ⟨E, hE⟩
  exact Nat.le_induction (P := fun m _ =>
    ∃ F : Hyper (r + 1) (Fin m), PairCancelling F) hbase hstep k (by omega)

/-- At every local level strictly above the arity, a single obstruction
defines an unbounded hereditary strong-amalgamation class which cannot be
defined by any family of smaller obstructions. -/
theorem strict_constrained_hierarchy (n k : ℕ) (hn : 3 ≤ n) (hk : n < k) :
    ∃ F : Hyper n (Fin k), PairCancelling F ∧
      (singleForbiddenClass F).Hereditary ∧
      (singleForbiddenClass F).Unbounded ∧
      (singleForbiddenClass F).HasSAP ∧
      (singleForbiddenClass F).KConstrained k ∧
      ¬ (singleForbiddenClass F).KConstrained (k - 1) := by
  obtain ⟨F, hF⟩ := exists_pairCancelling_every_size hn hk
  exact ⟨F, hF, singleForbiddenClass_hereditary F,
    singleForbiddenClass_unbounded hF, singleForbiddenClass_hasSAP hF,
    singleForbiddenClass_constrained F, singleForbiddenClass_not_constrained F (by omega)⟩

end Hypertournaments
