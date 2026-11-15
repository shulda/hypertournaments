import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Hypertournaments.Cochain

/-!
# Exact p3 mixed (n+1)-packet parity from two cone contractions

Let e be an arbitrary ZMod 2-valued orientation cochain on finite
subsets of a common ambient set, with two distinct fresh vertices l,r.
For an old subset Q avoiding both fresh points, the unsigned
coboundary of e on Q∪{l,r} decomposes into the two one-fresh links
e(Q∪{l}), e(Q∪{r}), and the coboundary of the mixed
double-cone cochain x=contractAt r (contractAt l e).

Thus if the genuine joint switching packet has even raw parity,
the exact mixed parity constraint is
  δx(Q) = e(Q∪{l}) + e(Q∪{r}).
This is the finite-set algebraic bridge used to gauge ALL possible
actual joint completions, rather than just preferred potential joints.

No random variables or AP assertions are used here.
-/

namespace Hypertournaments

/-- Exact unsigned coboundary on a two-new-vertex packet, with
all insertion and cochain contraction orders explicit. -/
theorem p3DoubleCone_packet_boundary
    {V : Type*} [DecidableEq V]
    (l r : V) (hlr : l ≠ r)
    (e : Finset V → ZMod 2)
    (Q : Finset V) (hl : l ∉ Q) (hr : r ∉ Q) :
    coboundary e (insert l (insert r Q)) =
      e (insert r Q) + e (insert l Q) +
      coboundary (contractAt r (contractAt l e)) Q := by
  have hnot : l ∉ insert r Q := by
    simp [hl, hlr]
  have hleft :=
    coboundary_insert_eq_add_contractAt l e (insert r Q) hnot
  have hright :=
    coboundary_insert_eq_add_contractAt
      r (contractAt l e) Q hr
  calc
    coboundary e (insert l (insert r Q)) =
        e (insert r Q) +
          coboundary (contractAt l e) (insert r Q) := hleft
    _ = e (insert r Q) +
        ((contractAt l e) Q +
          coboundary (contractAt r (contractAt l e)) Q) := by
            rw [hright]
    _ = e (insert r Q) + e (insert l Q) +
        coboundary (contractAt r (contractAt l e)) Q := by
      have hcontract : (contractAt l e) Q = e (insert l Q) := by
        simp [contractAt, hl]
      rw [hcontract]
      ring

/-- Vanishing of the true double-new packet coboundary gives the
exact mixed parity equation, without any preferred joint potential. -/
theorem p3DoubleCone_mixed_parity_of_zero
    {V : Type*} [DecidableEq V]
    (l r : V) (hlr : l ≠ r)
    (e : Finset V → ZMod 2)
    (Q : Finset V) (hl : l ∉ Q) (hr : r ∉ Q)
    (hzero : coboundary e (insert l (insert r Q)) = 0) :
    coboundary (contractAt r (contractAt l e)) Q =
      e (insert l Q) + e (insert r Q) := by
  have hb := p3DoubleCone_packet_boundary
    l r hlr e Q hl hr
  rw [hzero] at hb
  have hneg :
      coboundary (contractAt r (contractAt l e)) Q =
        -(e (insert r Q) + e (insert l Q)) :=
    eq_neg_of_add_eq_zero_right hb.symm
  have hchar (z : ZMod 2) : -z = z := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      -z = (1 - (2 : ZMod 2)) * z := by ring
      _ = z := by simp [htwo]
  calc
    coboundary (contractAt r (contractAt l e)) Q =
        -(e (insert r Q) + e (insert l Q)) := hneg
    _ = e (insert l Q) + e (insert r Q) := by
      rw [hchar]
      abel

end Hypertournaments
