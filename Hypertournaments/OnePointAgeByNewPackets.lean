import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.FinitePresentation

/-!
# One-point age membership reduces to packets containing its new point

For any intrinsic hypertournament arity n and age S, let an actual
side L on Fin(a+1) preserve an admissible old base A on Fin a.
Every packet avoiding the new vertex inherits its local index from
the old base. Thus full admissibility reduces to checking packets
that CONTAIN the sole new point.

No order, AP, or particular type family is assumed.
-/

namespace Hypertournaments

/-- If the old base is admissible and preserved, checking only
packets containing the new point suffices for side admissibility. -/
theorem onePoint_admissible_of_new_packets
    {n a : ℕ} (S : Set ℕ)
    (A : Hyper n (Fin a)) (L : Hyper n (Fin (a+1)))
    (hA : Admissible S A)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hnew : ∀ f : Fin (n+1) ↪ Fin (a+1),
      Fin.last a ∈ tupleVertices f → localIndex L f ∈ S) :
    Admissible S L := by
  intro f
  by_cases hcontains : Fin.last a ∈ tupleVertices f
  · exact hnew f hcontains
  · have hnot (i : Fin (n+1)) : f i ≠ Fin.last a := by
      intro hi
      apply hcontains
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    let g : Fin (n+1) ↪ Fin a := {
      toFun := fun i => ⟨(f i).val, by
        have hlt : (f i).val < a+1 := (f i).isLt
        have hne : (f i).val ≠ a := by
          intro hv
          apply hnot i
          apply Fin.ext
          exact hv
        omega⟩
      inj' := by
        intro i j hij
        apply f.injective
        apply Fin.ext
        exact congrArg (fun v : Fin a => v.val) hij
    }
    have htrans : g.trans (onePointBaseEmbedding a) = f := by
      ext i
      rfl
    have hidx : localIndex A g = localIndex L f := by
      rw [← htrans]
      exact localIndex_preserves A L (onePointBaseEmbedding a) hAL g
    rw [← hidx]
    exact hA g

end Hypertournaments
