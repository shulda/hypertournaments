import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.PartialHyper
import Hypertournaments.GeneralLocalIndexInvariant
import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.LocalPairCancellation

/-!
# Local-index classes as omission classes

A local restriction is exactly omission of the disallowed packets on
`n + 1` vertices. The forbidden family uses the existing intrinsic
orientations and arbitrary orientation-preserving vertex injections.
No finiteness or order on the ambient carrier is required.
-/

namespace Hypertournaments

/-- Admissibility descends along every orientation-preserving injection. -/
theorem admissible_of_preserves {n : ℕ} {V W : Type*} {S : Set ℕ}
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W}
    (h : Preserves A B e) (hB : Admissible S B) : Admissible S A := by
  intro t
  rw [localIndex_preserves A B e h t]
  exact hB (t.trans e)

/-- On one complete packet, every tuple has the index of the identity tuple. -/
theorem packet_admissible_iff_localIndex_mem {n : ℕ}
    (S : Set ℕ) (F : Hyper n (Fin (n + 1))) :
    Admissible S F ↔ localIndex F (Function.Embedding.refl _) ∈ S := by
  constructor
  · exact fun h => h (Function.Embedding.refl _)
  · intro h f
    let σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective f
      ⟨f.injective, Finite.surjective_of_injective f.injective⟩
    have hf : σ.toEmbedding.trans (Function.Embedding.refl _) = f := by
      ext i
      rfl
    rw [← hf, localIndex_perm_all]
    exact h

/-- Precisely the nonadmissible packets on `n + 1` vertices are forbidden. -/
def localForbiddenFamily (n : ℕ) (S : Set ℕ) : ForbiddenFamily n :=
  fun m => {F | m = n + 1 ∧ ¬ Admissible S F}

/-- The local-index formulation agrees with genuine induced-copy omission
on every carrier, including infinite and empty carriers. -/
theorem omits_localForbiddenFamily_iff_admissible {n : ℕ} {V : Type*}
    (S : Set ℕ) (A : Hyper n V) :
    Omits (localForbiddenFamily n S) A ↔ Admissible S A := by
  classical
  constructor
  · intro h t
    by_contra ht
    let F := A.pullback t
    have hF : ¬ Admissible S F := by
      intro hgood
      apply ht
      simpa only [F, localIndex_pullback, Function.Embedding.refl_trans] using
        hgood (Function.Embedding.refl _)
    exact h (n + 1) F ⟨rfl, hF⟩ t (fun _ => rfl)
  · intro h m F hF e hFE
    exact hF.2 (admissible_of_preserves hFE h)

/-- Allowing both central types makes every forbidden local packet genuinely
pair-cancelling. No validity restriction on phantom allowed indices is needed. -/
theorem localForbiddenFamily_pairCancelling {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S) :
    ∀ m (F : Hyper n (Fin m)), F ∈ localForbiddenFamily n S m → PairCancelling F := by
  intro m F hF
  rcases hF with ⟨rfl, hbad⟩
  have hnot : localIndex F (Function.Embedding.refl _) ∉ S := by
    intro h
    exact hbad ((packet_admissible_iff_localIndex_mem S F).mpr h)
  have hbound := localIndex_le_central F (Function.Embedding.refl _)
  have hnotCentral : localIndex F (Function.Embedding.refl _) ≠ centralIndex n := by
    intro h
    exact hnot (h.symm ▸ hcentral)
  have hnotNext : localIndex F (Function.Embedding.refl _) ≠ centralIndex n - 1 := by
    intro h
    exact hnot (h.symm ▸ hnext)
  exact pairCancelling_of_localIndex_le hn F (by omega)

end Hypertournaments
