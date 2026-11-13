import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1EvenRawAllowed
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# Local and global even-or-homogeneous certificates for the p1 age

For n=4k+5 the allowed local indices are the odd positive indices
together with the homogeneous index 0. The earlier true-hypertournament
parity theorem proves that an even raw orientation count forces an
odd positive local index. Here we add the complementary fact that
index zero itself belongs to the class and package both alternatives
into a reusable intrinsic side-admissibility criterion.

This reduces age membership of explicit one-point sides to checking
an even raw packet parity everywhere except for the two known right
homogeneous packets.
-/

namespace Hypertournaments

/-- Type zero is explicitly permitted by the n≡1 mod4
switching family with the zero type toggled. -/
theorem p1Zero_mem_toggleZero (k : ℕ) :
    (0 : ℕ) ∈ toggleZero (switchingAllowed (4*k+5)) := by
  change (0 : ℕ) ∉ switchingAllowed (4*k+5)
  intro h
  have hp := h.2
  unfold centralIndex at hp
  omega

/-- A genuine (n+1)-packet in arity 4k+5 is allowed whenever
its raw facet count is even or its local index is zero. -/
theorem Hyper.p1Toggle_allowed_of_raw_even_or_zero
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V)
    (h : (boolPacketPositiveCount (fun i : Fin (4*k+6) =>
        A.orient (facet f i)) % 2 = 0) ∨ localIndex A f = 0) :
    localIndex A f ∈ toggleZero (switchingAllowed (4*k+5)) := by
  rcases h with he | hz
  · exact A.p1Toggle_allowed_of_even_rawFacetCount k f he
  · rw [hz]
    exact p1Zero_mem_toggleZero k

/-- A complete true-hypertournament age proof can be reduced to
the even-or-zero check on increasing (n+1)-subsets only. -/
theorem Hyper.p1Toggle_admissible_of_ordered_even_or_zero
    (k a : ℕ) (A : Hyper (4*k+5) (Fin a))
    (h : ∀ Q : Finset (Fin a), ∀ hQ : Q.card = 4*k+6,
      let f : Fin (4*k+6) ↪o Fin a := Q.orderEmbOfFin hQ
      (boolPacketPositiveCount (fun i : Fin (4*k+6) =>
        A.orient (facet f.toEmbedding i)) % 2 = 0) ∨
        localIndex A f.toEmbedding = 0) :
    Admissible (toggleZero (switchingAllowed (4*k+5))) A := by
  apply (admissible_iff_canonical_all
    (toggleZero (switchingAllowed (4*k+5))) A).2
  intro Q hQ
  exact A.p1Toggle_allowed_of_raw_even_or_zero k
    (Q.orderEmbOfFin hQ).toEmbedding (h Q hQ)

end Hypertournaments
