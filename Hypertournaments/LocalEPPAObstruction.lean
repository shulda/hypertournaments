import Lean.Elab.Tactic.Omega
import Hypertournaments.EPPAKleinLift
import Hypertournaments.LocalKleinAutomorphisms
import Hypertournaments.KleinStabilizerRigidity

/-!
# The actual local obstruction to unrestricted finite EPPA

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. Two copies of one packet agree on their
base and have distinct last vertices. Four equal normalized base facets
produce the Klein action; ordinary EPPA would lift it honestly by Sylow.
No orientation involving both extra vertices is prescribed or used.
-/

namespace Hypertournaments

universe u v

/-- The source local EPPA obstruction, on any ambient carrier containing
the required span. Its conclusion excludes every unrestricted finite witness. -/
theorem local_eppa_obstruction {n : ℕ} {V : Type u}
    (hn : 4 ≤ n) (A : Hyper n V) (P : Hyper n (Fin (n + 1)))
    (f g : Fin (n + 1) ↪ V) (hf : Preserves P A f) (hg : Preserves P A g)
    (hagree : ∀ i : Fin n, f i.castSucc = g i.castSucc)
    (hdistinct : f (Fin.last n) ≠ g (Fin.last n))
    (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc) :
    ¬ A.HasFiniteEPPAWitness := by
  classical
  rintro ⟨b, B, e, hw⟩
  let ρ := packetKleinAutomorphisms P w hbits
  obtain ⟨σ, hσ⟩ := hw.lift_packet_action (by omega) P f hf ρ
  have hσinj : Function.Injective σ := by
    intro a c hac
    apply packetKleinAutomorphisms_injective P w hbits
    apply Hyper.Aut.ext
    intro i
    apply f.injective
    apply e.injective
    calc
      e (f ((ρ a : Equiv.Perm _) i)) = (σ a : Equiv.Perm _) (e (f i)) := (hσ a i).symm
      _ = (σ c : Equiv.Perm _) (e (f i)) :=
        congrArg (fun z : B.Aut => (z : Equiv.Perm _) (e (f i))) hac
      _ = e (f ((ρ c : Equiv.Perm _) i)) := hσ c i
  let s : Fin n ↪ Fin b := ⟨fun i => e (f i.castSucc), by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (n + 1) => z.val)
      (f.injective (e.injective hij)))⟩
  let x := e (f (Fin.last n))
  have hx : x ∉ Set.range s := by
    rintro ⟨i, hi⟩
    have hh := congrArg Fin.val (f.injective (e.injective hi))
    change i.val = n at hh
    omega
  have hσpoint : ∀ a, σ a • x = x := by
    intro a
    change (σ a : Equiv.Perm _) (e (f (Fin.last n))) = e (f (Fin.last n))
    rw [hσ, packetKleinAutomorphisms_last]
  have hσbase : ∀ a i, ∃ j, σ a • s i = s j := by
    intro a i
    have hne : (ρ a : Equiv.Perm _) i.castSucc ≠ Fin.last n := by
      intro hh
      have hlast : (ρ a : Equiv.Perm _) (Fin.last n) = Fin.last n :=
        packetKleinAutomorphisms_last P w hbits a
      have hv := congrArg (fun z : Fin (n + 1) => z.val)
        ((ρ a : Equiv.Perm (Fin (n + 1))).injective (hh.trans hlast.symm))
      change i.val = n at hv
      omega
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hne
    refine ⟨j, ?_⟩
    change (σ a : Equiv.Perm _) (e (f i.castSucc)) = e (f j.castSucc)
    rw [hσ, ← hj]
  have hσoutside : ∀ a i, i ∉ Set.range w → σ a • s i = s i := by
    intro a i hi
    change (σ a : Equiv.Perm _) (e (f i.castSucc)) = e (f i.castSucc)
    rw [hσ, packetKleinAutomorphisms_base_outside P w hbits a i hi]
  obtain ⟨γ, hγ⟩ := hw.extend_isomorphism P f g hf hg
  have hγbase : γ ∈ B.pointwiseStabilizer (Set.range s) := by
    apply Hyper.mem_pointwiseStabilizer_iff.mpr
    rintro _ ⟨i, rfl⟩
    change (γ : Equiv.Perm _) (e (f i.castSucc)) = e (f i.castSucc)
    rw [hγ, ← hagree]
  have hfix := klein_pointwiseStabilizer_fixes B hn s x hx w σ hσinj
    hσbase hσpoint hσoutside ⟨γ, hγbase⟩
  change (γ : Equiv.Perm _) (e (f (Fin.last n))) = e (f (Fin.last n)) at hfix
  exact hdistinct (e.injective (hfix.symm.trans (hγ (Fin.last n))))

/-- The obstruction excludes witnesses on arbitrary finite carriers and in
any universe, using the proved finite-presentation transport. -/
theorem local_eppa_obstruction_no_witness {n : ℕ} {V : Type u} {W : Type v}
    (hn : 4 ≤ n) (A : Hyper n V) (P : Hyper n (Fin (n + 1)))
    (f g : Fin (n + 1) ↪ V) (hf : Preserves P A f) (hg : Preserves P A g)
    (hagree : ∀ i : Fin n, f i.castSucc = g i.castSucc)
    (hdistinct : f (Fin.last n) ≠ g (Fin.last n))
    (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc)
    (B : Hyper n W) (e : V ↪ W) : ¬ A.IsEPPAWitness B e := by
  intro h
  exact local_eppa_obstruction hn A P f g hf hg hagree hdistinct w hbits
    h.hasFiniteEPPAWitness

end Hypertournaments
