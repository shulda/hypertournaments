import Hypertournaments.Affine.FiberCoding
import Hypertournaments.Affine.LinearOperations

/-!
# Intrinsic potential equations and effective labels

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". A potential determines the effective
labels. The raw palette may have fibers with several different labels.
-/

universe u v w z

namespace Hypertournaments.Affine

variable {Q : Type u} {G : Type v} [AddCommGroup G] {d : Data Q G}

theorem Closed.pullback {n : ℕ} {V : Type w} {W : Type z}
    {raw : Labelled n d.palette W} (h : Closed d raw) (e : V ↪ W) :
    Closed d (raw.pullback e) := by
  intro t
  exact h (t.trans e)

theorem IsPotential.pullback {r : ℕ} {V : Type w} {W : Type z}
    {raw : Labelled (r + 1) d.palette W}
    {p : Labelled r (Palette.affine d.offset) W}
    (h : IsPotential d raw p) (e : V ↪ W) :
    IsPotential d (raw.pullback e) (p.pullback e) := by
  intro t
  exact h (t.trans e)

/-- The potential equation implies closedness on every actual tuple. -/
theorem IsPotential.closed {r : ℕ} {V : Type w}
    {raw : Labelled (r + 1) d.palette V}
    {p : Labelled r (Palette.affine d.offset) V} (h : IsPotential d raw p) :
    Closed d raw := by
  intro t
  have heq : signedCoboundary (fun s => d.effective (raw.label s)) t =
      signedCoboundary (signedCoboundary p.label) t := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : G => (-1 : ℤ) ^ i.val • x) (h (facet t i)).symm
  rw [heq]
  exact signedCoboundary_signedCoboundary_zero p.label t

/-- Preserving a chosen potential preserves its effective upper labels. -/
theorem IsPotential.effective_preserves {r : ℕ} {V : Type w} {W : Type z}
    {rawV : Labelled (r + 1) d.palette V} {rawW : Labelled (r + 1) d.palette W}
    {pV : Labelled r (Palette.affine d.offset) V}
    {pW : Labelled r (Palette.affine d.offset) W}
    (hV : IsPotential d rawV pV) (hW : IsPotential d rawW pW)
    {e : V ↪ W} (hp : pV.Preserves pW e) :
    (d.effectiveLabelled rawV).Preserves (d.effectiveLabelled rawW) e := by
  intro t
  change d.effective (rawW.label (t.trans e)) = d.effective (rawV.label t)
  rw [← hW (t.trans e), ← hV t]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x : G => (-1 : ℤ) ^ i.val • x) (hp (facet t i))

/-- Differences of two potentials of the same raw structure are closed
ordinary alternating cochains. -/
theorem IsPotential.affineSub_closed {r : ℕ} {V : Type w}
    {raw : Labelled (r + 1) d.palette V}
    {p q : Labelled r (Palette.affine d.offset) V}
    (hp : IsPotential d raw p) (hq : IsPotential d raw q)
    (t : Fin (r + 1) ↪ V) : signedCoboundary (p.affineSub q).label t = 0 := by
  change signedCoboundary (fun s => p.label s - q.label s) t = 0
  rw [signedCoboundary_sub, hp t, hq t, sub_self]

end Hypertournaments.Affine
