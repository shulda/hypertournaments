import Mathlib.Tactic.Ext
import Hypertournaments.TwoPadNaturality

/-!
# Exact commuting-square law for intrinsic two-pad tuples

Suppose a source vertex set U embeds into a lower joint W, while a
lifted source vertex set V embeds into a higher joint Z.  Assume the
two paths from U to Z commute, and two padding vertices p,q of V map
to padding vertices outside the image of W.

Then forming the two-pad tuple on the source and embedding it into Z
is exactly the same injective (n+2)-tuple as first mapping the old
tuple into W and padding it in Z.

This geometric identity is the exact bridge required when a proposed
higher ordinary amalgam preserves the lifted source orientations:
the orientation on the recovered lower side then agrees with the
original source orientation, independently of any linear ordering.
-/

namespace Hypertournaments

/-- A two-pad tuple respects an arbitrary commutative square of
injective vertex maps. The two side lengths and arities are arbitrary. -/
theorem twoPadSliceTuple_commuting_square
    {n : ℕ} {U W V Z : Type*}
    (f : U ↪ W) (g : W ↪ Z)
    (h : U ↪ V) (j : V ↪ Z)
    (hsquare : h.trans j = f.trans g)
    (p q : V)
    (hp : p ∉ Set.range h) (hq : q ∉ Set.range h)
    (hpq : p ≠ q)
    (hp' : j p ∉ Set.range g) (hq' : j q ∉ Set.range g)
    (t : Fin n ↪ U) :
    (twoPadSliceTuple h p q hp hq hpq t).trans j =
      twoPadSliceTuple g (j p) (j q) hp' hq'
        (fun he => hpq (j.injective he)) (t.trans f) := by
  ext k
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun i => ?_) l) k
  · simp [twoPadSliceTuple]
  · simp [twoPadSliceTuple]
  · simpa [twoPadSliceTuple] using
      (DFunLike.congr_fun hsquare (t i))

/-- Orientation recovery is preserved when passing from a lifted
source side to an arbitrary higher-arity joint through a commuting
square of vertex embeddings. This is valid for ordinary embeddings
and never uses a common auxiliary vertex order. -/
theorem twoPad_source_recovery_of_preserves
    {n : ℕ} {U W V Z : Type*}
    (A : Hyper n U) (B : Hyper (n + 2) V) (D : Hyper (n + 2) Z)
    (f : U ↪ W) (g : W ↪ Z)
    (h : U ↪ V) (j : V ↪ Z)
    (hsquare : h.trans j = f.trans g)
    (p q : V)
    (hp : p ∉ Set.range h) (hq : q ∉ Set.range h)
    (hpq : p ≠ q)
    (hp' : j p ∉ Set.range g) (hq' : j q ∉ Set.range g)
    (hBD : Preserves B D j)
    (hsource : ∀ t : Fin n ↪ U,
      B.orient (twoPadSliceTuple h p q hp hq hpq t) = A.orient t)
    (t : Fin n ↪ U) :
    D.orient (twoPadSliceTuple g (j p) (j q) hp' hq'
      (fun he => hpq (j.injective he)) (t.trans f)) = A.orient t := by
  have hmap := twoPadSliceTuple_commuting_square
    f g h j hsquare p q hp hq hpq hp' hq' t
  calc
    D.orient (twoPadSliceTuple g (j p) (j q) hp' hq'
        (fun he => hpq (j.injective he)) (t.trans f)) =
      D.orient ((twoPadSliceTuple h p q hp hq hpq t).trans j) :=
        congrArg D.orient hmap.symm
    _ = B.orient (twoPadSliceTuple h p q hp hq hpq t) :=
      hBD (twoPadSliceTuple h p q hp hq hpq t)
    _ = A.orient t := hsource t

end Hypertournaments
