import Hypertournaments.OddToggleP1ExplicitSides
import Hypertournaments.OddToggleP1CoreRows

/-!
# Exact parity of the uniform p1 common-base facet bits

The common base contains 4k auxiliary pads followed by six core
vertices. Its raw signs on the facets obtained by omitting one base
vertex are positive everywhere except at the two core vertices
a2 and a4. Therefore there are exactly 4k+4 positive signs,
an even number.

The proof is uniform in k and uses only the literal base bit table;
it is a prerequisite for certifying the actual common-base
hypertournament's membership in the toggle-zero allowed class.
-/

namespace Hypertournaments

/-- Precisely the two core vertices a2 and a4 have negative
prescribed raw base signs. -/
theorem p1BaseVertexBit_false_iff (k : ℕ) (v : Fin (4*k+6)) :
    p1BaseVertexBit k v = false ↔
      v = p1CoreAt k (2 : Fin 6) ∨
      v = p1CoreAt k (4 : Fin 6) := by
  have hv := v.isLt
  by_cases hp : v.val < 4*k
  · simp [p1BaseVertexBit, hp, p1CoreAt, Fin.ext_iff]
    omega
  · simp [p1BaseVertexBit, hp, p1CoreAt, Fin.ext_iff]
    omega

/-- The exact set of positive raw base signs is the universe with
the two exceptional core vertices removed. -/
theorem p1BasePositiveSet (k : ℕ) :
    (Finset.univ.filter (fun v : Fin (4*k+6) =>
      p1BaseVertexBit k v = true)) =
    ((Finset.univ : Finset (Fin (4*k+6))).erase
      (p1CoreAt k (2 : Fin 6))).erase
      (p1CoreAt k (4 : Fin 6)) := by
  ext v
  have hbit :
      p1BaseVertexBit k v = true ↔
        v ≠ p1CoreAt k (2 : Fin 6) ∧
        v ≠ p1CoreAt k (4 : Fin 6) := by
    constructor
    · intro ht
      have hfalse : p1BaseVertexBit k v ≠ false := by
        simp [ht]
      have hn : ¬(v = p1CoreAt k (2 : Fin 6) ∨
          v = p1CoreAt k (4 : Fin 6)) := by
        intro hd
        exact hfalse ((p1BaseVertexBit_false_iff k v).mpr hd)
      exact ⟨fun hd => hn (Or.inl hd), fun hd => hn (Or.inr hd)⟩
    · intro hn
      cases hv : p1BaseVertexBit k v
      · exact False.elim
          (((p1BaseVertexBit_false_iff k v).mp hv).elim hn.1 hn.2)
      · rfl
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true, and_comm] using hbit

/-- The entire common-base raw packet contains exactly 4k+4
positive signs, and in particular has even raw parity. -/
theorem p1BaseVertexBit_positiveCount (k : ℕ) :
    boolPacketPositiveCount
      (fun v : Fin (4*k+6) => p1BaseVertexBit k v) = 4*k+4 := by
  let v2 : Fin (4*k+6) := p1CoreAt k (2 : Fin 6)
  let v4 : Fin (4*k+6) := p1CoreAt k (4 : Fin 6)
  have hne : v2 ≠ v4 := by
    intro he
    have hv := congrArg Fin.val he
    change 4*k+2 = 4*k+4 at hv
    omega
  have hmem2 :
      v2 ∈ (Finset.univ : Finset (Fin (4*k+6))) := Finset.mem_univ _
  have hmem4 :
      v4 ∈ (Finset.univ : Finset (Fin (4*k+6))).erase v2 :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
  have hcard2 :
      ((Finset.univ : Finset (Fin (4*k+6))).erase v2).card + 1 =
        4*k+6 := by
    simpa using Finset.card_erase_add_one hmem2
  have hcard4 :
      (((Finset.univ : Finset (Fin (4*k+6))).erase v2).erase v4).card + 1 =
        ((Finset.univ : Finset (Fin (4*k+6))).erase v2).card := by
    exact Finset.card_erase_add_one hmem4
  change (Finset.univ.filter (fun v : Fin (4*k+6) =>
    p1BaseVertexBit k v = true)).card = 4*k+4
  rw [p1BasePositiveSet]
  change (((Finset.univ : Finset (Fin (4*k+6))).erase v2).erase v4).card =
    4*k+4
  omega

theorem p1BaseVertexBit_even (k : ℕ) :
    (boolPacketPositiveCount
      (fun v : Fin (4*k+6) => p1BaseVertexBit k v)) % 2 = 0 := by
  rw [p1BaseVertexBit_positiveCount]
  omega

end Hypertournaments
