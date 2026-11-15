import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3ActualPunctureSubsetInjective

/-!
# Real W and link coefficient tables from the exact global source space

The certified global finite counting experiment uses Boolean source
assignments on the disjoint union of full W-transversal indices and
punctured link indices. The genuine canonical p3 sides instead accept
coefficient functions on *actual finite subsets of Fin((s+1)*t)*.

The true full-transversal and puncture source-index maps are both
injective, so any global Boolean assignment can be extended to
ZMod 2-valued coefficients on all old finite subsets. On every
selected zero-sum trial this extension agrees with the exact
p3FullTrialSourceIndex used in global counting. Off the selected
code it is zero; this is legitimate because the canonical sides
permit arbitrary potential coefficients.

No stochastic assumption, joint completion or AP assertion is
required for this exact source-to-potential bridge.
-/

namespace Hypertournaments

/-- Extend a ZMod 2-valued function along an injective source
index map by assigning zero outside its image. -/
noncomputable def p3ExtendByIndex
    {A B : Type*} (f : A → B) (g : A → ZMod 2) (y : B) : ZMod 2 := by
  classical
  exact if h : ∃ x : A, f x = y then g (Classical.choose h) else 0

/-- Exact evaluation on the image of an injective source map.
No choice of inverse or proof witness affects the value. -/
theorem p3ExtendByIndex_at
    {A B : Type*} (f : A → B) (g : A → ZMod 2)
    (hf : Function.Injective f) (x : A) :
    p3ExtendByIndex f g (f x) = g x := by
  classical
  have he : ∃ x' : A, f x' = f x := ⟨x, rfl⟩
  change (if h : ∃ x' : A, f x' = f x then
      g (Classical.choose h) else 0) = g x
  rw [dif_pos he]
  have hcho : Classical.choose he = x :=
    hf (Classical.choose_spec he)
  rw [hcho]

/-- The genuine base potential coefficient W(U) obtained from
a Boolean assignment on the full global W/link source space. -/
noncomputable def p3RealWFromSources
    (s t : ℕ) (ht : 0 < t)
    (bits : p3FullSourceSpace (ZMod t) s → Bool) :
    Finset (Fin ((s+1)*t)) → ZMod 2 :=
  p3ExtendByIndex
    (fun q : p3SelectedTrials (ZMod t) s =>
      p3CoordinateTransversal (s+1) t ht q.1)
    (fun q : p3SelectedTrials (ZMod t) s =>
      p1BitToZMod (bits (p3FullTrialSourceIndex s (q, Sum.inr ()))))

/-- The genuine single missing-block link coefficient table
on old finite subsets. This is a shared raw table for L/R;
the two canonical sides read it only at their respective
eligible missing blocks. -/
noncomputable def p3RealLinkFromSources
    (s t : ℕ) (ht : 0 < t)
    (bits : p3FullSourceSpace (ZMod t) s → Bool) :
    Finset (Fin ((s+1)*t)) → ZMod 2 :=
  p3ExtendByIndex
    (p3ActualPunctureSubsetIndex s t ht)
    (fun qi : p3SelectedTrials (ZMod t) s × Fin (s+1) =>
      p1BitToZMod
        (bits (p3FullTrialSourceIndex s (qi.1, Sum.inl qi.2))))

/-- The real W-coefficient of each selected full transversal is
exactly its independent global full-source bit. -/
theorem p3RealWFromSources_selected
    (s t : ℕ) (ht : 0 < t)
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) :
    p3RealWFromSources s t ht bits
        (p3CoordinateTransversal (s+1) t ht q.1) =
      p1BitToZMod
        (bits (p3FullTrialSourceIndex s (q, Sum.inr ()))) := by
  unfold p3RealWFromSources
  apply p3ExtendByIndex_at
  intro q r hqr
  apply Subtype.ext
  exact p3CoordinateTransversal_injective (s+1) t ht hqr

/-- The real punctured L/R potential coefficient of each
selected zero-sum trial is exactly its independent global
link-source bit, with no extra missing-block label given to
the potential. -/
theorem p3RealLinkFromSources_selected
    (s t : ℕ) (ht : 0 < t)
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (qi : p3SelectedTrials (ZMod t) s × Fin (s+1)) :
    p3RealLinkFromSources s t ht bits
        (p3ActualPunctureSubsetIndex s t ht qi) =
      p1BitToZMod
        (bits (p3FullTrialSourceIndex s (qi.1, Sum.inl qi.2))) := by
  unfold p3RealLinkFromSources
  apply p3ExtendByIndex_at
  exact p3ActualPunctureSubsetIndex_injective s t ht

end Hypertournaments
