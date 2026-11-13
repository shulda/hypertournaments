import Hypertournaments.OddToggleP3SourceFlipHalf
import Hypertournaments.OddToggleP3FullSourceUniform
import Hypertournaments.OddToggleP3GlobalAllTrialsExact
import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Exact half-disagreement event for one selected zero-sum p3 transversal

A selected zero-sum transversal has m independent link-source
bits indexed by deleted coordinates. For any chosen coordinate,
the parity of the OTHER link bits does not change when that one
source bit is flipped. Therefore the XOR of the chosen link bit
and the parity of all other link bits is true for exactly half of
the entire finite global W/link assignment space.

This is a genuine zero-sum/full-source indexing statement,
not merely a claim about unrelated synthetic random bits.
The eventual intrinsic identification obstruction still needs
the side orientation-link sum alpha+beta to be identified with
this selected link parity.
-/

namespace Hypertournaments

/-- XOR-parity of all link coordinates OTHER than one selected
coordinate, expressed by the exact ZMod 2/Bool bit conversion. -/
def p3OtherSelectedLinkParity
    {B : Type*} [DecidableEq B]
    (m : ℕ) (source : Fin m → B) (chosen : Fin m)
    (bits : B → Bool) : Bool :=
  p3ZMod2ToBool
    (∑ i ∈ (Finset.univ : Finset (Fin m)).erase chosen,
      p1BitToZMod (bits (source i)))

/-- The other-link parity is invariant under flipping only the
chosen source bit when the source index map is injective. -/
theorem p3OtherSelectedLinkParity_flip_invariant
    {B : Type*} [DecidableEq B]
    (m : ℕ) (source : Fin m → B)
    (hsource : Function.Injective source)
    (chosen : Fin m) (bits : B → Bool) :
    p3OtherSelectedLinkParity m source chosen
        (p3FlipSelectedBit (source chosen) bits) =
      p3OtherSelectedLinkParity m source chosen bits := by
  unfold p3OtherSelectedLinkParity
  apply congrArg p3ZMod2ToBool
  apply Finset.sum_congr rfl
  intro i hi
  have hine : i ≠ chosen := (Finset.mem_erase.mp hi).1
  have hsourceNe : source i ≠ source chosen := by
    intro heq
    exact hine (hsource heq)
  simp [p3FlipSelectedBit, hsourceNe]

/-- Exactly half of all global Boolean assignments have odd
parity on a chosen finite injectively indexed link-source family,
for any nonempty number of links. Stated via a distinguished bit
XOR the F₂ parity of all remaining links, without probability. -/
theorem p3SelectedLinkParity_half
    {B : Type*} [Fintype B] [DecidableEq B]
    (m : ℕ) (source : Fin m → B)
    (hsource : Function.Injective source)
    (chosen : Fin m) :
    2 * Nat.card {bits : B → Bool //
      ((bits (source chosen) ^^
        p3OtherSelectedLinkParity m source chosen bits) = true)} =
      2 ^ (Fintype.card B) := by
  exact p3HalfXorEvent_of_flipInvariant
    (source chosen)
    (p3OtherSelectedLinkParity m source chosen)
    (p3OtherSelectedLinkParity_flip_invariant
      m source hsource chosen)

/-- Every fixed selected zero-sum transversal in the FULL p3
global source space has an exact half-sized odd-link event.
All other global W and link bits are left unconstrained. -/
theorem p3ZeroSumFullSource_fixedTrial_linkParity_half
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (q : p3SelectedTrials G s)
    (chosen : Fin (s+1)) :
    let source : Fin (s+1) → p3FullSourceSpace G s :=
      fun i => p3FullTrialSourceIndex s (q, Sum.inl i)
    2 * Nat.card {bits : p3FullSourceSpace G s → Bool //
      ((bits (source chosen) ^^
        p3OtherSelectedLinkParity (s+1) source chosen bits) = true)} =
      2 ^ (Fintype.card (p3FullSourceSpace G s)) := by
  classical
  intro source
  have hsource : Function.Injective source := by
    intro i j heq
    change p3FullTrialSourceIndex (G:=G) s (q, Sum.inl i) =
      p3FullTrialSourceIndex (G:=G) s (q, Sum.inl j) at heq
    have hprod :
        (q, (Sum.inl i : Fin (s+1) ⊕ Unit)) =
          (q, (Sum.inl j : Fin (s+1) ⊕ Unit)) :=
      (p3FullTrialSourceIndex_injective (G:=G) s) heq
    exact Sum.inl.inj (congrArg Prod.snd hprod)
  exact p3SelectedLinkParity_half
    (s+1) source hsource chosen

end Hypertournaments
