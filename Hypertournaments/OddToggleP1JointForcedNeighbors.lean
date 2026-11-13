import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1ActualJointSymmetry
import Hypertournaments.OddToggleP1ActualMixedSupport

/-!
# Degree-two forced-edge calculus for the actual p1 canonical joint

The genuine zero-or-two homogeneous-neighbor relation of a
hypothetical admissible joint is symmetric. If a4 has the forced
neighbor left-new and no other possible neighbor except a2,
it must also be adjacent to a2. Then a2 has that neighbor;
if its only possible other neighbor is a5, its degree must
be exactly two and it must also be adjacent to a5.

This turns the finite combinatorial part of the obstruction into
a general elementary Finset lemma and one intrinsic theorem
whose remaining hypotheses concern precise neighbor support.
-/

namespace Hypertournaments

/-- A two-element finite set supported on at most a,b and containing
a must also contain b. -/
theorem p1_second_of_two_supported
    {V : Type*} [DecidableEq V]
    (S : Finset V) (a b : V)
    (ha : a ∈ S) (hsupport : ∀ x ∈ S, x = a ∨ x = b)
    (hcard : S.card = 2) :
    b ∈ S := by
  by_contra hb
  have hsub : S ⊆ ({a} : Finset V) := by
    intro x hx
    rcases hsupport x hx with hxa | hxb
    · simpa only [Finset.mem_singleton] using hxa
    · subst x
      exact (hb hx).elim
  have hle : S.card ≤ 1 := by
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_singleton] using hc
  omega

/-- The actual zero-or-two neighbor degrees force both decisive
core-core edges from a single external fixed edge and the two
localized neighbor-support premises. -/
theorem p1JointCore_forced_neighbors_of_support
    (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+5))) E)
    (hfixed4 :
      p1JointLeftNew k ∈
        p1JointHomogeneousNeighbors k E
          (p1JointOld k (p1CoreAt k (4 : Fin 6))))
    (hsupport4 : ∀ y,
      y ∈ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6))) →
      y = p1JointLeftNew k ∨
      y = p1JointOld k (p1CoreAt k (2 : Fin 6)))
    (hsupport2 : ∀ y,
      y ∈ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6))) →
      y = p1JointOld k (p1CoreAt k (4 : Fin 6)) ∨
      y = p1JointOld k (p1CoreAt k (5 : Fin 6))) :
    p1JointOld k (p1CoreAt k (2 : Fin 6)) ∈
      p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6))) ∧
    p1JointOld k (p1CoreAt k (5 : Fin 6)) ∈
      p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6))) := by
  let u : Fin (4*k+6+2) := p1JointLeftNew k
  let a2 : Fin (4*k+6+2) := p1JointOld k (p1CoreAt k (2 : Fin 6))
  let a4 : Fin (4*k+6+2) := p1JointOld k (p1CoreAt k (4 : Fin 6))
  let a5 : Fin (4*k+6+2) := p1JointOld k (p1CoreAt k (5 : Fin 6))
  have h4two :
      (p1JointHomogeneousNeighbors k E a4).card = 2 := by
    rcases p1JointHomogeneousNeighbors_zero_or_two k E hE a4 with hz | ht
    · have hp : 0 < (p1JointHomogeneousNeighbors k E a4).card :=
        Finset.card_pos.mpr ⟨u, hfixed4⟩
      omega
    · exact ht
  have h42 : a2 ∈ p1JointHomogeneousNeighbors k E a4 :=
    p1_second_of_two_supported
      (p1JointHomogeneousNeighbors k E a4) u a2
      hfixed4 hsupport4 h4two
  have h24 : a4 ∈ p1JointHomogeneousNeighbors k E a2 :=
    p1JointHomogeneousNeighbors_symmetric k E a4 a2 h42
  have h2two :
      (p1JointHomogeneousNeighbors k E a2).card = 2 := by
    rcases p1JointHomogeneousNeighbors_zero_or_two k E hE a2 with hz | ht
    · have hp : 0 < (p1JointHomogeneousNeighbors k E a2).card :=
        Finset.card_pos.mpr ⟨a4, h24⟩
      omega
    · exact ht
  have h25 : a5 ∈ p1JointHomogeneousNeighbors k E a2 :=
    p1_second_of_two_supported
      (p1JointHomogeneousNeighbors k E a2) a4 a5
      h24 hsupport2 h2two
  exact ⟨h42, h25⟩

end Hypertournaments
