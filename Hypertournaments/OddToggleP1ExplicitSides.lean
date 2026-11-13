import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1CanonicalLinks
import Hypertournaments.CanonicalSignPresentation
import Hypertournaments.EvenSuspensionBaseCompatibility

/-!
# Explicit source and side sign tables for the odd p1 obstruction

Let n=4k+5, m=4k and a=m+6. The common base is Fin a; both
one-point sides have Fin(a+1), with the new endpoint at Fin.last a.

The p1 manuscript specifies base signs b_v and left/right link
matrices with a noncanonical order for the left endpoint.
The canonical-link module normalizes both sides to the common
order with endpoint last, so a finite-set sign-table definition
describes the two actual intrinsic hypertournaments.

For a base n-set Q the omitted base set has size one, and the sign
is b_v. For a side n-set containing the endpoint, two base vertices
are omitted and the sign is the canonical link bit for that pair.
Wrong-sized table entries are dummy values.

The first preservation theorem is unconditional: both sides have
exactly the same induced common base in the intrinsic language.
Side admissibility and nonamalgamation remain separate obligations.
-/

namespace Hypertournaments

/-- Raw base facet sign for each base vertex. -/
def p1BaseVertexBit (k : ℕ) (v : Fin (4*k+6)) : Bool :=
  if v.val < 4*k then true
  else decide (v.val - 4*k ≠ 2 ∧ v.val - 4*k ≠ 4)

/-- Missing old base vertices of a one-point-side subset. -/
def p1MissingBase (k : ℕ)
    (Q : Finset (Fin (4*k+6+1))) : Finset (Fin (4*k+6)) :=
  Finset.univ.filter (fun v : Fin (4*k+6) =>
    (v.castSucc : Fin (4*k+6+1)) ∉ Q)

/-- XOR of the base signs over all omitted old vertices. -/
def p1BaseMissingBit (k : ℕ)
    (M : Finset (Fin (4*k+6))) : Bool :=
  decide (((M.filter (fun v => p1BaseVertexBit k v = true)).card) % 2 = 1)

/-- XOR of canonical links over all unordered omitted pairs.
On a two-element missing set this is exactly that pair's link. -/
def p1PairMissingBit (k : ℕ) (left : Bool)
    (M : Finset (Fin (4*k+6))) : Bool :=
  decide ((∑ v ∈ M,
    (M.filter (fun w => v < w ∧ p1CanonicalLink k left v w = true)).card)
      % 2 = 1)

/-- Common-base finite sign table. -/
def p1BaseSignTable (k : ℕ)
    (Q : Finset (Fin (4*k+6))) : Bool :=
  p1BaseMissingBit k (Finset.univ \ Q)

/-- Left/right finite sign tables with the endpoint last. -/
def p1SideSignTable (k : ℕ) (left : Bool)
    (Q : Finset (Fin (4*k+6+1))) : Bool :=
  if Fin.last (4*k+6) ∈ Q then
    p1PairMissingBit k left (p1MissingBase k Q)
  else
    p1BaseMissingBit k (p1MissingBase k Q)

/-- Actual intrinsic hypertournaments from the finite tables. -/
def p1BaseHyper (k : ℕ) : Hyper (4*k+5) (Fin (4*k+6)) :=
  Hyper.fromOrderedSigns (p1BaseSignTable k)

def p1SideHyper (k : ℕ) (left : Bool) :
    Hyper (4*k+5) (Fin (4*k+6+1)) :=
  Hyper.fromOrderedSigns (p1SideSignTable k left)

/-- No embedded old vertex is the side's last vertex. -/
theorem p1Last_not_mem_base_image (k : ℕ)
    (Q : Finset (Fin (4*k+6))) :
    Fin.last (4*k+6) ∉
      Q.image (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)) := by
  intro h
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
  have hlt : v.val < 4*k+6 := v.isLt
  have heq : v.val = 4*k+6 := by
    have hvVal := congrArg Fin.val hv
    change v.val = 4*k+6 at hvVal
    exact hvVal
  omega

/-- Canonical inclusion transports missing old vertices exactly. -/
theorem p1MissingBase_of_base_image (k : ℕ)
    (Q : Finset (Fin (4*k+6))) :
    p1MissingBase k
      (Q.image (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1))) =
      Finset.univ \ Q := by
  ext v
  have hmem :
      (v.castSucc : Fin (4*k+6+1)) ∈
        Q.image (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)) ↔
      v ∈ Q := by
    constructor
    · intro hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      have he : u = v :=
        (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)).injective huv
      simpa [he] using hu
    · intro hv
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  simp only [p1MissingBase, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr hmem

/-- Both sides agree on the source sign table on every embedded
old subset, including wrong-sized dummy entries. -/
theorem p1SideSignTable_image_base (k : ℕ) (left : Bool)
    (Q : Finset (Fin (4*k+6))) :
    p1SideSignTable k left
      (Q.image (Fin.castSuccOrderEmb : Fin (4*k+6) ↪o Fin (4*k+6+1))) =
      p1BaseSignTable k Q := by
  have hn := p1Last_not_mem_base_image k Q
  have hm := p1MissingBase_of_base_image k Q
  change (if Fin.last (4*k+6) ∈
    Q.image (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1))
    then p1PairMissingBit k left
      (p1MissingBase k (Q.image Fin.castSuccEmb))
    else p1BaseMissingBit k (p1MissingBase k (Q.image Fin.castSuccEmb))) =
    p1BaseMissingBit k (Finset.univ \ Q)
  simp only [if_neg hn, hm]

/-- The two concrete sides have the same actual induced
common-base hypertournament. -/
theorem p1SideHyper_preserves_base (k : ℕ) (left : Bool) :
    Preserves (p1BaseHyper k) (p1SideHyper k left)
      (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)) := by
  exact fromOrderedSigns_preserves
    (Fin.castSuccOrderEmb : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (p1BaseSignTable k) (p1SideSignTable k left)
    (p1SideSignTable_image_base k left)

end Hypertournaments
