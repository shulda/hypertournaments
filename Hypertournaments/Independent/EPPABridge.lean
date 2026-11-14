import Hypertournaments.Independent.ClassBridge
import Hypertournaments.EPPAConsequences
import Hypertournaments.EvenNoEPPA

/-!
# The independent EPPA targets

The independent total-map presentation of a partial automorphism is connected
to every actual subset isomorphism. The witness and its inclusion are fixed
before that partial automorphism is chosen. All three introductory targets
are then consequences of the existing intrinsic negative theorems.
-/

namespace IndependentHypertournaments.Bridge

universe u

/-- Present an independently specified class in the native language. -/
def nativeClass {n : ℕ} (K : FiniteHT n → Prop) :
    Hypertournaments.FiniteHyperClass n :=
  fun m => {A | K ⟨m, ofHyper A⟩}

/-- A native subset isomorphism has a total-map representative. Outside its
source we use the identity, which also works on an empty carrier. -/
noncomputable def partialTotal {n : ℕ} {V : Type u}
    {A : Hypertournaments.Hyper n V} (p : A.PartialAutomorphism) : V → V := by
  classical
  exact fun x => if hx : x ∈ p.source then (p.equiv ⟨x, hx⟩ : V) else x

@[simp] theorem partialTotal_apply_of_mem {n : ℕ} {V : Type u}
    {A : Hypertournaments.Hyper n V} (p : A.PartialAutomorphism)
    (x : V) (hx : x ∈ p.source) :
    partialTotal p x = (p.equiv ⟨x, hx⟩ : V) := by
  classical
  simp only [partialTotal, dite_eq_left hx]

@[simp] theorem partialTotal_source {n : ℕ} {V : Type u}
    {A : Hypertournaments.Hyper n V} (p : A.PartialAutomorphism)
    (x : p.source) : partialTotal p x = (p.equiv x : V) :=
  partialTotal_apply_of_mem p x x.property

/-- In particular, quantifying over independent partial automorphisms covers
every native partial automorphism, with no nonemptiness assumption. -/
theorem partialTotal_isPartialAutomorphism {n : ℕ} {V : Type u}
    {A : Hypertournaments.Hyper n V} (p : A.PartialAutomorphism) :
    PartialAutomorphism (ofHyper A) p.source p.target (partialTotal p) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [partialTotal_apply_of_mem p a ha]
    exact (p.equiv ⟨a, ha⟩).property
  · intro a b ha hb hab
    have he : p.equiv ⟨a, ha⟩ = p.equiv ⟨b, hb⟩ := by
      apply Subtype.ext
      simpa only [partialTotal_apply_of_mem p a ha,
        partialTotal_apply_of_mem p b hb] using hab
    exact congrArg Subtype.val (p.equiv.injective he)
  · intro b hb
    let a : p.source := p.equiv.symm ⟨b, hb⟩
    refine ⟨a, a.property, ?_⟩
    rw [partialTotal_source]
    exact congrArg Subtype.val (p.equiv.apply_symm_apply ⟨b, hb⟩)
  · intro t hD
    by_cases ht : Function.Injective t
    · let e : Fin n ↪ p.source :=
        ⟨fun i => ⟨t i, hD i⟩, fun i j hij => ht (congrArg Subtype.val hij)⟩
      let s : Fin n ↪ V := e.trans (Hypertournaments.subsetEmbedding p.source)
      let r : Fin n ↪ V :=
        (e.trans p.equiv.toEmbedding).trans (Hypertournaments.subsetEmbedding p.target)
      have hs : (s : Fin n → V) = t := rfl
      have hr : (r : Fin n → V) = fun i => partialTotal p (t i) := by
        funext i
        exact (partialTotal_apply_of_mem p (t i) (hD i)).symm
      rw [← hr, ← hs, ofHyper_orientation, ofHyper_orientation]
      exact congrArg Hypertournaments.p1BitToZMod (p.preserves e)
    · have hp : ¬ Function.Injective (fun i => partialTotal p (t i)) := by
        intro hp
        apply ht
        intro i j hij
        exact hp (congrArg (partialTotal p) hij)
      rw [(ofHyper A).degenerate _ hp, (ofHyper A).degenerate _ ht]

/-- An independent EPPA witness is an actual native EPPA witness. This proves
the difficult direction needed by the three negative target statements. -/
theorem hasEPPA_to_nativeClass {n : ℕ} (K : FiniteHT n → Prop)
    (h : HasEPPA K) : Hypertournaments.ClassHasEPPA (nativeClass K) := by
  classical
  intro a A hA
  obtain ⟨B, hB, inclusion, hi, hext⟩ := h ⟨a, ofHyper A⟩ hA
  let e : Fin a ↪ Fin B.1 := ⟨inclusion, hi.1⟩
  refine ⟨B.1, toHyper B.2, e, ?_, ⟨inferInstance, ?_, ?_⟩⟩
  · change K ⟨B.1, ofHyper (toHyper B.2)⟩
    simpa only [ofHyper_toHyper] using hB
  · have hh := (embeds_iff_preserves (ofHyper A) B.2 e).mp hi
    simpa only [toHyper_ofHyper] using hh
  · intro p
    obtain ⟨g, hg, hgp⟩ := hext p.source p.target (partialTotal p)
      (partialTotal_isPartialAutomorphism p)
    let σ : Equiv.Perm (Fin B.1) := Equiv.ofBijective g hg.1
    have hσ : Hypertournaments.Preserves (toHyper B.2) (toHyper B.2)
        σ.toEmbedding :=
      (embeds_iff_preserves B.2 B.2 σ.toEmbedding).mp ⟨σ.injective, hg.2⟩
    refine ⟨⟨σ, hσ⟩, ?_⟩
    intro x
    change g (inclusion x.val) = inclusion (p.equiv x).val
    simpa only [partialTotal_source] using hgp x.val x.property

theorem hereditary_to_nativeClass {n : ℕ} (K : FiniteHT n → Prop)
    (h : Hereditary K) : Hypertournaments.ClassHereditary (nativeClass K) := by
  intro a b A B e he hB
  apply h ⟨a, ofHyper A⟩ ⟨b, ofHyper B⟩ hB
  refine ⟨e, (embeds_iff_preserves (ofHyper A) (ofHyper B) e).mpr ?_⟩
  simpa only [toHyper_ofHyper] using he

theorem unbounded_to_nativeClass {n : ℕ} (K : FiniteHT n → Prop)
    (h : Unbounded K) : Hypertournaments.ClassUnbounded (nativeClass K) := by
  intro N
  obtain ⟨A, hA, hN⟩ := h N
  refine ⟨A.1, hN, toHyper A.2, ?_⟩
  change K ⟨A.1, ofHyper (toHyper A.2)⟩
  simpa only [ofHyper_toHyper] using hA

theorem strongAmalgamation_to_nativeClass {n : ℕ} (K : FiniteHT n → Prop)
    (h : StrongAmalgamation K) :
    Hypertournaments.ClassHasStrongAmalgamation (nativeClass K) := by
  intro a b c A B C hA hB hC f g hf hg
  have hfi : Embeds (ofHyper A) (ofHyper B) f :=
    (embeds_iff_preserves (ofHyper A) (ofHyper B) f).mpr
      (by simpa only [toHyper_ofHyper] using hf)
  have hgi : Embeds (ofHyper A) (ofHyper C) g :=
    (embeds_iff_preserves (ofHyper A) (ofHyper C) g).mpr
      (by simpa only [toHyper_ofHyper] using hg)
  obtain ⟨D, hD, i, j, hi, hj, hcomm, hinter⟩ :=
    h ⟨a, ofHyper A⟩ ⟨b, ofHyper B⟩ ⟨c, ofHyper C⟩ hA hB hC f g hfi hgi
  let ie : Fin b ↪ Fin D.1 := ⟨i, hi.1⟩
  let je : Fin c ↪ Fin D.1 := ⟨j, hj.1⟩
  refine ⟨D.1, toHyper D.2, ie, je, ?_, ?_, ?_, hcomm, hinter⟩
  · change K ⟨D.1, ofHyper (toHyper D.2)⟩
    simpa only [ofHyper_toHyper] using hD
  · have hh := (embeds_iff_preserves (ofHyper B) D.2 ie).mp hi
    simpa only [toHyper_ofHyper] using hh
  · have hh := (embeds_iff_preserves (ofHyper C) D.2 je).mp hj
    simpa only [toHyper_ofHyper] using hh

/-- Article thm:intro-eppa(i), with precisely the independent hypotheses. -/
theorem independent_intro_eppa_part_i : IntroEPPAPartI := by
  intro n hn K hU hHer hSAP hEPPA
  exact Hypertournaments.unbounded_hereditary_SAP_not_EPPA hn (nativeClass K)
    (hereditary_to_nativeClass K hHer) (strongAmalgamation_to_nativeClass K hSAP)
    (unbounded_to_nativeClass K hU) (hasEPPA_to_nativeClass K hEPPA)

/-- Article thm:intro-eppa(ii), including the empty forbidden family. -/
theorem independent_intro_eppa_part_ii : IntroEPPAPartII := by
  intro n hn F hpc hEPPA
  apply Hypertournaments.pair_cancelling_not_EPPA hn (nativeFamily F)
    (nativeFamily_pairCancelling F hpc)
  have hnative := hasEPPA_to_nativeClass (Forb F) hEPPA
  intro a A hA
  have hAi : Forb F ⟨a, ofHyper A⟩ :=
    (omits_iff F (ofHyper A)).mp (by simpa only [toHyper_ofHyper] using hA)
  obtain ⟨b, B, e, hB, hw⟩ := hnative a A hAi
  refine ⟨b, B, e, ?_, hw⟩
  have hh := (omits_iff F (ofHyper B)).mpr hB
  simpa only [toHyper_ofHyper] using hh

/-- Article thm:intro-eppa(iii), for all finite even 5-hypertournaments. -/
theorem independent_intro_eppa_part_iii : IntroEPPAPartIII := by
  intro hEPPA
  apply Hypertournaments.even_five_not_hasEPPA
  have hnative := hasEPPA_to_nativeClass (fun A : FiniteHT 5 => IsEven A.2) hEPPA
  intro a A hA
  have hEven : A.IsEven :=
    (A.admissible_switching_iff_isEven (by decide)).mp
      ((Hypertournaments.omits_localForbiddenFamily_iff_admissible _ A).mp hA)
  have hAi : IsEven (ofHyper A) := (isEven_iff (ofHyper A)).mpr
    (by simpa only [toHyper_ofHyper] using hEven)
  obtain ⟨b, B, e, hB, hw⟩ := hnative a A hAi
  refine ⟨b, B, e, ?_, hw⟩
  have hEvenB : B.IsEven := by
    have hh := (isEven_iff (ofHyper B)).mp hB
    simpa only [toHyper_ofHyper] using hh
  exact (Hypertournaments.omits_localForbiddenFamily_iff_admissible _ B).mpr
    ((B.admissible_switching_iff_isEven (by decide)).mpr hEvenB)

end IndependentHypertournaments.Bridge

namespace IndependentHypertournaments

/-- All three independently specified introductory EPPA targets. -/
theorem intro_eppa : IntroEPPAStatement :=
  ⟨Bridge.independent_intro_eppa_part_i, Bridge.independent_intro_eppa_part_ii,
    Bridge.independent_intro_eppa_part_iii⟩

end IndependentHypertournaments
