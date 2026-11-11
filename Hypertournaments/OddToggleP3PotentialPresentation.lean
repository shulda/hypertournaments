import Hypertournaments.OddToggleP1ActualCoboundary
import Hypertournaments.OddToggleP1BooleanParity
import Hypertournaments.DoubleCoboundary

/-!
# Intrinsic hypertournaments presented by finite F₂ potentials

An arbitrary ZMod 2 potential z on finite subsets determines a
Boolean sign table by taking the unsigned coboundary and converting
the resulting bit back to Bool. A finite intrinsic hypertournament
is obtained from its ordered-sign presentation.

On every n-set, the canonical sign-table entry has exactly the
prescribed F₂ value. Consequently its actual orientation cochain
has zero coboundary on all (n+1)-sets by δδ=0.

This holds in any arity, without assumptions on z. The next
p3 module converts the zero coboundary into switchingAllowed
membership and treats protected nonhomogeneous packets separately.
-/

namespace Hypertournaments

/-- The Boolean bit represented by an element of the two-element
field. -/
def p3ZMod2ToBool (x : ZMod 2) : Bool := decide (x = 1)

/-- Converting ZMod 2 to Bool and back preserves every field element. -/
theorem p3BitToZMod_roundtrip (x : ZMod 2) :
    p1BitToZMod (p3ZMod2ToBool x) = x := by
  have h : ∀ y : ZMod 2,
      p1BitToZMod (p3ZMod2ToBool y) = y := by decide
  exact h x

/-- The sign of each unordered set is the F₂ boundary of the given
potential, written as a Boolean orientation. -/
def p3PotentialSign {a : ℕ}
    (z : Finset (Fin a) → ZMod 2) (Q : Finset (Fin a)) : Bool :=
  p3ZMod2ToBool (coboundary z Q)

/-- The actual intrinsic hypertournament defined by a potential
on subsets, for any arity n. -/
def p3HyperFromPotential (n a : ℕ)
    (z : Finset (Fin a) → ZMod 2) : Hyper n (Fin a) :=
  Hyper.fromOrderedSigns (p3PotentialSign z)

/-- On an n-set, the canonical sign of the intrinsic structure is
exactly the prescribed potential coboundary bit. -/
theorem p3HyperFromPotential_canonical
    (n a : ℕ) (z : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin a)) (hQ : Q.card = n) :
    (p3HyperFromPotential n a z).canonicalSignTable Q =
      p3PotentialSign z Q := by
  rw [Hyper.canonicalSignTable_at (p3HyperFromPotential n a z) Q hQ]
  change (Hyper.fromOrderedSigns (p3PotentialSign z)).orient
    (Q.orderEmbOfFin hQ).toEmbedding = p3PotentialSign z Q
  rw [fromOrderedSigns_orient_strictMono (p3PotentialSign z)
    (Q.orderEmbOfFin hQ).toEmbedding (Q.orderEmbOfFin hQ).strictMono]
  simpa [tupleVertices] using
    (congrArg (p3PotentialSign z)
      (Finset.image_orderEmbOfFin_univ Q hQ))

/-- The canonical orientation bit on any n-set agrees with
the F₂ coboundary of the source potential, without losing an
orientation or choosing a different normalization. -/
theorem p3HyperFromPotential_canonicalZMod
    (n a : ℕ) (z : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin a)) (hQ : Q.card = n) :
    p1BitToZMod
      ((p3HyperFromPotential n a z).canonicalSignTable Q) =
      coboundary z Q := by
  rw [p3HyperFromPotential_canonical n a z Q hQ]
  exact p3BitToZMod_roundtrip _

/-- The actual canonical orientation cochain of a potential-induced
hypertournament has zero coboundary on every increasing packet,
by the already certified double-coboundary identity. -/
theorem p3HyperFromPotential_rawCoboundary_zero
    (n a : ℕ) (z : Finset (Fin a) → ZMod 2)
    (f : Fin (n+1) ↪o Fin a) :
    coboundary
      (fun Q => p1BitToZMod
        ((p3HyperFromPotential n a z).canonicalSignTable Q))
      (tupleVertices f.toEmbedding) = 0 := by
  let S := tupleVertices f.toEmbedding
  have hcard : S.card = n+1 := by
    dsimp [S, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hsum :
      coboundary
        (fun Q => p1BitToZMod
          ((p3HyperFromPotential n a z).canonicalSignTable Q)) S =
        coboundary (coboundary z) S := by
    unfold coboundary
    apply Finset.sum_congr rfl
    intro v hv
    have hQ : (S.erase v).card = n := by
      have hh := Finset.card_erase_add_one hv
      omega
    exact p3HyperFromPotential_canonicalZMod n a z (S.erase v) hQ
  calc
    coboundary
      (fun Q => p1BitToZMod
        ((p3HyperFromPotential n a z).canonicalSignTable Q))
      (tupleVertices f.toEmbedding) =
        coboundary (coboundary z) S := hsum
    _ = 0 := coboundary_coboundary_zero z S

end Hypertournaments
