import Hypertournaments.OddToggleP1Core
import Hypertournaments.DoubleCoboundary

/-!
# Universal phase obstruction for three homogeneous facets

This is the combinatorial half of the zero-or-two principle in the
n ≡ 1 (mod 4) exceptional construction. It is deliberately separated
from the double-coboundary parity argument.

For a parent set with n+2 ordered points, deleting a vertex i produces
an (n+1)-packet. If that packet is homogeneous, its raw n-facet signs
alternate along its intrinsic increasing coordinate positions, with
some Boolean phase b_i. Deleting j from that packet has coordinate
j when j<i and coordinate j-1 when i<j.

The two resulting deletions represent the same n-set. For i<j,
equating their signs forces (b_i xor parity(i)) and
(b_j xor parity(j)) to be different. Three distinct homogeneous
deleted packets are therefore impossible, since Bool has two values.

All statements here are about exact raw signs on finite sets.
Connecting a concrete Hyper's homogeneous localIndex=0 to the
raw-alternating hypothesis is a separate geometric bridge.
-/

namespace Hypertournaments

/-- Position of vertex j inside the increasing tuple obtained by
erasing i from an increasing (n+2)-tuple. The caller assumes i≠j. -/
def p1ErasePosition {n : ℕ} (i j : Fin (n+2)) : ℕ :=
  if j < i then j.val else j.val - 1

/-- Two single-vertex erasures commute, a fact used to compare
the raw orientation of the same shared n-subset. -/
theorem p1EraseTwice_comm {n : ℕ} (i j : Fin (n+2)) :
    ((Finset.univ : Finset (Fin (n+2))).erase i).erase j =
      ((Finset.univ : Finset (Fin (n+2))).erase j).erase i := by
  ext v
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- Consecutive positive integer indices have opposite parities. -/
theorem p1IndexPredParity (j : ℕ) (hj : 0 < j) :
    decide ((j-1)%2=1) = !(decide (j%2=1)) := by
  by_cases hp : j%2=1
  · have hn : (j-1)%2≠1 := by omega
    simp [hp, hn]
  · have hn : (j-1)%2=1 := by omega
    simp [hp, hn]

/-- A Boolean equality with the second parity bit complemented
forces the two parity-adjusted phases to disagree. -/
theorem p1BoolIncompatiblePhases
    (a b p q : Bool) (h : (a ^^ (!q)) = (b ^^ p)) :
    (a ^^ p) ≠ (b ^^ q) := by
  cases a <;> cases b <;> cases p <;> cases q <;> simp_all

/-- Homogeneous (n+1)-packets on erased vertices can never occupy
three distinct deletions. In fact the alternating phases define
an injection from the homogeneous deletions to Bool. -/
theorem p1RawHomogeneous_card_le_two
    (n : ℕ)
    (raw : Finset (Fin (n+2)) → Bool)
    (H : Fin (n+2) → Prop) [DecidablePred H]
    (phase : Fin (n+2) → Bool)
    (hraw : ∀ i, H i → ∀ j, j ≠ i →
      raw (((Finset.univ : Finset (Fin (n+2))).erase i).erase j) =
        (phase i ^^ decide ((p1ErasePosition i j)%2=1))) :
    (Finset.univ.filter H).card ≤ 2 := by
  classical
  let colour : Fin (n+2) → Bool :=
    fun i => phase i ^^ decide (i.val%2=1)
  have hpair (i j : Fin (n+2))
      (hi : H i) (hj : H j) (hne : i ≠ j) :
      colour i ≠ colour j := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hrawij := hraw i hi j (ne_of_gt hij)
      have hrawji := hraw j hj i (ne_of_lt hij)
      rw [p1EraseTwice_comm i j] at hrawij
      have hnot : ¬ j < i := not_lt.mpr (le_of_lt hij)
      simp only [p1ErasePosition, if_neg hnot, if_pos hij] at hrawij hrawji
      have heq := hrawij.symm.trans hrawji
      have hjpos : 0 < j.val := by
        have hiLt : i.val < j.val := hij
        omega
      have hpar := p1IndexPredParity j.val hjpos
      rw [hpar] at heq
      exact p1BoolIncompatiblePhases (phase i) (phase j)
        (decide (i.val%2=1)) (decide (j.val%2=1)) heq
    · have hrev : colour j ≠ colour i :=
        by
          have hrawji := hraw j hj i (ne_of_gt hji)
          have hrawij := hraw i hi j (ne_of_lt hji)
          rw [p1EraseTwice_comm j i] at hrawji
          have hnot : ¬ i < j := not_lt.mpr (le_of_lt hji)
          simp only [p1ErasePosition, if_neg hnot, if_pos hji] at hrawji hrawij
          have heq := hrawji.symm.trans hrawij
          have hipos : 0 < i.val := by
            have hjLt : j.val < i.val := hji
            omega
          have hpar := p1IndexPredParity i.val hipos
          rw [hpar] at heq
          exact p1BoolIncompatiblePhases (phase j) (phase i)
            (decide (j.val%2=1)) (decide (i.val%2=1)) heq
      exact Ne.symm hrev
  have hinjective :
      Function.Injective
        (fun x : {i : Fin (n+2) // H i} => colour x.val) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    exact (hpair x.val y.val x.property y.property hne) hxy
  have hcard : Fintype.card {i : Fin (n+2) // H i} ≤
      Fintype.card Bool :=
    Fintype.card_le_of_injective
      (fun x : {i : Fin (n+2) // H i} => colour x.val) hinjective
  simpa [Fintype.card_subtype] using hcard

/-- The parity identity (supplied by δ²=0) together with the
phase obstruction gives exactly zero or two homogeneous deletions. -/
theorem p1Abstract_zero_or_two
    (n : ℕ)
    (raw : Finset (Fin (n+2)) → Bool)
    (H : Fin (n+2) → Prop) [DecidablePred H]
    (phase : Fin (n+2) → Bool)
    (hraw : ∀ i, H i → ∀ j, j ≠ i →
      raw (((Finset.univ : Finset (Fin (n+2))).erase i).erase j) =
        (phase i ^^ decide ((p1ErasePosition i j)%2=1)))
    (heven : (Finset.univ.filter H).card%2 = 0) :
    (Finset.univ.filter H).card = 0 ∨
      (Finset.univ.filter H).card = 2 := by
  have hle := p1RawHomogeneous_card_le_two n raw H phase hraw
  omega

end Hypertournaments
