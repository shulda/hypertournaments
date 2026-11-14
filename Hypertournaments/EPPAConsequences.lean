import Lean.Elab.Tactic.Omega
import Hypertournaments.LocalEPPAObstruction
import Hypertournaments.StrongSelfAmalgam
import Hypertournaments.FourEqualPacket
import Hypertournaments.PairCancellingWitnessClass
import Hypertournaments.LocalTypeRealization

/-!
# Class-level consequences of the local EPPA obstruction

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:higharity-no-eppa`. The hereditary/SAP statement is for arbitrary
finite classes; omission classes are a separately proved instance.
Every obstruction produced below has exactly n+2 vertices and excludes
finite witnesses even in the unrestricted class.
-/

namespace Hypertournaments

/-- A hereditary SAP class containing a packet with four equal normalized
facets contains an actual n+2-vertex unrestricted EPPA obstruction. -/
theorem exists_class_EPPA_obstruction_of_four_equal {n : ℕ} (hn : 4 ≤ n)
    (K : FiniteHyperClass n) (hHer : ClassHereditary K)
    (hSAP : ClassHasStrongAmalgamation K)
    (P : Hyper n (Fin (n + 1))) (hP : P ∈ K (n + 1))
    (hfour : HasFourEqualFacets P) :
    ∃ D : Hyper n (Fin (n + 2)), D ∈ K (n + 2) ∧ ¬ D.HasFiniteEPPAWitness := by
  obtain ⟨σ, w, hw⟩ := reindex_four_equal_to_base hn P hfour
  let Q := P.pullback σ.toEmbedding
  have hQ : Q ∈ K (n + 1) := hHer Q P σ.toEmbedding (fun _ => rfl) hP
  obtain ⟨D, hD, hf, hg⟩ := hSAP.self_amalgam_packet hHer Q hQ
  refine ⟨D, hD, local_eppa_obstruction hn D Q
    (leftJointInclusion n) (rightJointInclusion n) hf hg ?_ ?_ w ?_⟩
  · intro i
    exact (rightJointInclusion_old n i).symm
  · rw [rightJointInclusion_new]
    exact Fin.castSucc_ne_last (Fin.last n)
  · intro i j
    exact (hw i).trans (hw j).symm

/-- The numerical local-type condition in the article supplies the four
equal facets without requiring a preferred representative. -/
theorem exists_class_EPPA_obstruction_of_localIndex {n : ℕ} (hn : 4 ≤ n)
    (K : FiniteHyperClass n) (hHer : ClassHereditary K)
    (hSAP : ClassHasStrongAmalgamation K)
    (P : Hyper n (Fin (n + 1))) (hP : P ∈ K (n + 1))
    (hindex : localIndex P (Function.Embedding.refl _) ≤ n - 3) :
    ∃ D : Hyper n (Fin (n + 2)), D ∈ K (n + 2) ∧ ¬ D.HasFiniteEPPAWitness :=
  exists_class_EPPA_obstruction_of_four_equal hn K hHer hSAP P hP
    (hasFourEqualFacets_of_localIndex_le P hindex (by omega))

/-- Seven packet entries suffice, so every unbounded hereditary SAP class
in arity at least six contains a fixed-size unrestricted EPPA obstruction. -/
theorem exists_class_EPPA_obstruction_of_unbounded {n : ℕ} (hn : 6 ≤ n)
    (K : FiniteHyperClass n) (hHer : ClassHereditary K)
    (hSAP : ClassHasStrongAmalgamation K) (hU : ClassUnbounded K) :
    ∃ D : Hyper n (Fin (n + 2)), D ∈ K (n + 2) ∧ ¬ D.HasFiniteEPPAWitness := by
  obtain ⟨m, hm, A, hA⟩ := hU (n + 1)
  let e : Fin (n + 1) ↪ Fin m := (Fin.castLEOrderEmb hm).toEmbedding
  let P := A.pullback e
  have hP : P ∈ K (n + 1) := hHer P A e (fun _ => rfl) hA
  exact exists_class_EPPA_obstruction_of_four_equal (by omega) K hHer hSAP P hP
    (hasFourEqualFacets_of_six_le hn P)

/-- The unrestricted obstruction excludes class-level ordinary EPPA. -/
theorem unbounded_hereditary_SAP_not_EPPA {n : ℕ} (hn : 6 ≤ n)
    (K : FiniteHyperClass n) (hHer : ClassHereditary K)
    (hSAP : ClassHasStrongAmalgamation K) (hU : ClassUnbounded K) :
    ¬ ClassHasEPPA K := by
  obtain ⟨D, hD, hbad⟩ := exists_class_EPPA_obstruction_of_unbounded hn K hHer hSAP hU
  exact not_classHasEPPA_of_unrestricted_obstruction K D hD hbad

theorem hereditary_SAP_not_EPPA_of_localIndex {n : ℕ} (hn : 4 ≤ n)
    (K : FiniteHyperClass n) (hHer : ClassHereditary K)
    (hSAP : ClassHasStrongAmalgamation K)
    (P : Hyper n (Fin (n + 1))) (hP : P ∈ K (n + 1))
    (hindex : localIndex P (Function.Embedding.refl _) ≤ n - 3) : ¬ ClassHasEPPA K := by
  obtain ⟨D, hD, hbad⟩ := exists_class_EPPA_obstruction_of_localIndex hn K hHer hSAP P hP hindex
  exact not_classHasEPPA_of_unrestricted_obstruction K D hD hbad

/-- One n+2-vertex obstruction omits every finite pair-cancelling structure. -/
theorem exists_all_pair_cancelling_EPPA_obstruction {n : ℕ} (hn : 4 ≤ n) :
    ∃ D : Hyper n (Fin (n + 2)),
      Omits (allPairCancellingFamily n) D ∧ ¬ D.HasFiniteEPPAWitness := by
  let P := localTypeRepresentative n (centralIndex n - 1)
  have hidx : localIndex P (Function.Embedding.refl _) = centralIndex n - 1 :=
    localIndex_localTypeRepresentative n _ (Nat.sub_le _ _)
  have hP : Omits (allPairCancellingFamily n) P :=
    omits_allPairCancelling_of_packet_index (by omega) P (by rw [hidx])
  have hsmall : localIndex P (Function.Embedding.refl _) ≤ n - 3 := by
    rw [hidx]
    unfold centralIndex
    omega
  exact exists_class_EPPA_obstruction_of_localIndex hn (omissionClass (allPairCancellingFamily n))
    (omissionClass_hereditary _) (allPairCancellingFamily_hasStrongAmalgamation (by omega))
    P hP hsmall

/-- The same finite witness works simultaneously for every pair-cancelling
forbidden family, including the empty family. -/
theorem exists_common_pair_cancelling_EPPA_obstruction {n : ℕ} (hn : 4 ≤ n) :
    ∃ D : Hyper n (Fin (n + 2)),
      (∀ (family : ForbiddenFamily n),
        (∀ m F, F ∈ family m → PairCancelling F) → Omits family D) ∧
      ¬ D.HasFiniteEPPAWitness := by
  obtain ⟨D, hD, hbad⟩ := exists_all_pair_cancelling_EPPA_obstruction hn
  exact ⟨D, fun family hpc => omits_allPairCancelling_implies family hpc D hD, hbad⟩

/-- Every pair-cancelling omission class fails ordinary EPPA in arity at
least four; the finite obstruction is valid even against unrestricted targets. -/
theorem pair_cancelling_not_EPPA {n : ℕ} (hn : 4 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    ¬ HasEPPA family := by
  obtain ⟨D, hD, hbad⟩ := exists_common_pair_cancelling_EPPA_obstruction hn
  exact not_hasEPPA_of_unrestricted_obstruction family D (hD family hpc) hbad

end Hypertournaments
