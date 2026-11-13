import Lean.Elab.Tactic.Omega
import Hypertournaments.CanonicalPacket
import Hypertournaments.EvenAlternatingBalance

/-!
# Intrinsic centrality of an ordered three-pad packet

Suppose that in an increasing (2k+3)-tuple the first three
facet raw signs agree, while every later facet is positively oriented.
The normalized facet vector is then precisely
(b,!b,b) followed by the alternating length-2k Boolean vector.
Its minority local type is central k+1, regardless of b.

This is a general orientation-level lemma, independent of the
geometric proof that the concrete even suspension has this shape.
-/

namespace Hypertournaments

/-- The exact central local type of a true hypertournament
on an increasing (2k+3)-tuple with the three-pad raw-sign shape. -/
theorem localIndex_ordered_threePad_central
    (k : ℕ) {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool)
    (f : Fin (2 * k + 3) ↪o V) (b : Bool)
    (hpad : ∀ i : Fin (2 * k + 3), i.val < 3 →
      signs (tupleVertices (facet f.toEmbedding i)) = b)
    (hold : ∀ i : Fin (2 * k + 3), 3 ≤ i.val →
      signs (tupleVertices (facet f.toEmbedding i)) = true) :
    localIndex (Hyper.fromOrderedSigns (n := 2 * k + 2) signs)
      f.toEmbedding = k + 1 := by
  let D : Hyper (2 * k + 2) V :=
    Hyper.fromOrderedSigns signs
  have hraw (i : Fin (2 * k + 3)) :
      D.orient (facet f.toEmbedding i) =
        signs (tupleVertices (facet f.toEmbedding i)) :=
    fromOrderedSigns_facet_increasing signs f i
  have h0 :
      normalizedFacet D f.toEmbedding (0 : Fin (2 * k + 3)) = b := by
    unfold normalizedFacet
    rw [hraw 0, hpad 0 (by simp only [Fin.val_zero]; omega)]
    simp
  have h1 :
      normalizedFacet D f.toEmbedding
        ((0 : Fin (2 * k + 2)).succ) = !b := by
    unfold normalizedFacet
    rw [hraw _, hpad _ (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
    cases b <;> simp [Fin.val_succ, Fin.val_zero]
  have h2 :
      normalizedFacet D f.toEmbedding
        ((0 : Fin (2 * k + 1)).succ.succ) = b := by
    unfold normalizedFacet
    rw [hraw _, hpad _ (by simp only [Fin.val_succ, Fin.val_zero]; omega)]
    change (b ^^ decide ((2 % (2 * k + 2 + 1)) % 2 = 1)) = b
    have hlt : 2 < 2 * k + 2 + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    simp
  have htail (j : Fin (2 * k)) :
      normalizedFacet D f.toEmbedding j.succ.succ.succ =
        decide (j.val % 2 = 1) := by
    have hpos : D.orient (facet f.toEmbedding j.succ.succ.succ) =
        true := (hraw _).trans (hold _ (by
          simp only [Fin.val_succ]
          all_goals omega))
    unfold normalizedFacet
    rw [hpos]
    simp only [Fin.val_succ]
    by_cases hj : j.val % 2 = 1
    · have hne : (j.val + 1 + 1 + 1) % 2 ≠ 1 := by omega
      simp [hj, hne]
    · have heq : (j.val + 1 + 1 + 1) % 2 = 1 := by omega
      simp [hj, heq]
  have hbits :
      (fun i : Fin (2 * k + 3) => normalizedFacet D f.toEmbedding i) =
      Fin.cons b (Fin.cons (!b) (Fin.cons b
        (fun j : Fin (2 * k) => decide (j.val % 2 = 1)))) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_
      (fun j => Fin.cases ?_ (fun t => ?_) j) i) i
    · simpa only [Fin.cons_zero] using h0
    · simpa only [Fin.cons_succ, Fin.cons_zero] using h1
    · simpa only [Fin.cons_succ, Fin.cons_zero] using h2
    · simpa only [Fin.cons_succ] using htail t
  change
    min (boolPacketPositiveCount
        (fun i : Fin (2 * k + 3) => normalizedFacet D f.toEmbedding i))
      ((2 * k + 3) -
        boolPacketPositiveCount
          (fun i : Fin (2 * k + 3) => normalizedFacet D f.toEmbedding i))
      = k + 1
  rw [hbits]
  exact boolPacketMinority_even_suspension_three_pads k b

end Hypertournaments
