import Hypertournaments.OddToggleP3SingletonDoubleSingletonGap
import Hypertournaments.OddToggleP3SingletonPositions
import Hypertournaments.OddToggleP3ProtectedTriple

/-!
# Three consecutive protected block fibers have opposite-parity singletons

For a monotone sorted packet word, suppose three consecutive labels
u,u+1,u+2 are all represented, and together occur at most four times.
Either two adjacent block labels are singleton, or the occupancy
pattern is singleton-double-singleton. The first two cases use the
certified consecutive-singleton position lemma; the last case uses
the exact odd-gap theorem proved for the doubled middle label.

Thus there are always TWO vertices of opposite deletion parity,
each globally unique in its block label and among the three
protected labels. This is the exact order geometry for the
q=m full-block fresh-side case, prior to actual side support.
-/

namespace Hypertournaments

/-- If a label occupies one position in a finite word, that
position is globally unique among all word positions. -/
theorem p3SingletonFiber_global_unique
    {N : ℕ} (block : Fin N → ℕ) (label : ℕ)
    (hcard : (Finset.univ.filter
      (fun z : Fin N => block z = label)).card = 1)
    (x : Fin N) (hx : block x = label) :
    ∀ z : Fin N, block z = label → z = x := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ (Finset.univ.filter
      (fun z : Fin N => block z = label)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  rw [hw] at hxmem
  have hxw : x = w := by simpa using hxmem
  intro z hz
  have hzmem : z ∈ (Finset.univ.filter
      (fun u : Fin N => block u = label)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  rw [hw] at hzmem
  have hzw : z = w := by simpa using hzmem
  exact hzw.trans hxw.symm

/-- Protected block labels u,u+1,u+2 of total occupancy ≤4
always yield two globally singleton vertices of opposite parity
in the actual sorted positions. Both selected labels lie in
this protected triple, not elsewhere in the word. -/
theorem p3Monotone_protectedTriple_oppositeParity_singletons
    {N : ℕ} (block : Fin N → ℕ) (hmono : Monotone block)
    (u : ℕ)
    (ha : 0 < (Finset.univ.filter
      (fun z : Fin N => block z = u)).card)
    (hb : 0 < (Finset.univ.filter
      (fun z : Fin N => block z = u+1)).card)
    (hc : 0 < (Finset.univ.filter
      (fun z : Fin N => block z = u+2)).card)
    (hsum :
      (Finset.univ.filter
        (fun z : Fin N => block z = u)).card +
      (Finset.univ.filter
        (fun z : Fin N => block z = u+1)).card +
      (Finset.univ.filter
        (fun z : Fin N => block z = u+2)).card ≤ 4) :
    ∃ x y : Fin N,
      x.val % 2 ≠ y.val % 2 ∧
      (block x = u ∨ block x = u+1 ∨ block x = u+2) ∧
      (block y = u ∨ block y = u+1 ∨ block y = u+2) ∧
      (∀ z : Fin N, block z = block x → z = x) ∧
      (∀ z : Fin N, block z = block y → z = y) := by
  classical
  let A : Finset (Fin N) :=
    Finset.univ.filter (fun z => block z = u)
  let B : Finset (Fin N) :=
    Finset.univ.filter (fun z => block z = u+1)
  let C : Finset (Fin N) :=
    Finset.univ.filter (fun z => block z = u+2)
  have ha' : 0 < A.card := ha
  have hb' : 0 < B.card := hb
  have hc' : 0 < C.card := hc
  have hsum' : A.card+B.card+C.card≤4 := hsum
  rcases p3ProtectedTriple_patterns A.card B.card C.card
      ha' hb' hc' hsum' with
    ⟨hA1,hB1⟩ | ⟨hB1,hC1⟩ | ⟨hA1,hB2,hC1⟩
  · obtain ⟨x,y,hx,hy,_,hpar⟩ :=
      p3ConsecutiveSingletonFibers_oppositeParity
        N block hmono u hA1 hB1
    have hmod : x.val%2 ≠ y.val%2 := by
      intro heq
      exact hpar (congrArg (fun z : ℕ => decide (z=1)) heq)
    refine ⟨x,y,hmod,Or.inl hx,Or.inr (Or.inl hy),?_,?_⟩
    · exact p3SingletonFiber_global_unique block u hA1 x hx
    · exact p3SingletonFiber_global_unique block (u+1) hB1 y hy
  · obtain ⟨x,y,hx,hy,_,hpar⟩ :=
      p3ConsecutiveSingletonFibers_oppositeParity
        N block hmono (u+1) hB1 (by simpa only [show (u+1)+1=u+2 by omega] using hC1)
    have hy' : block y = u+2 := by omega
    have hmod : x.val%2 ≠ y.val%2 := by
      intro heq
      exact hpar (congrArg (fun z : ℕ => decide (z=1)) heq)
    refine ⟨x,y,hmod,Or.inr (Or.inl hx),Or.inr (Or.inr hy'),?_,?_⟩
    · exact p3SingletonFiber_global_unique block (u+1) hB1 x hx
    · exact p3SingletonFiber_global_unique block (u+2) hC1 y hy'
  · obtain ⟨x,hAx⟩ := Finset.card_eq_one.mp hA1
    obtain ⟨y,hCy⟩ := Finset.card_eq_one.mp hC1
    have hxmem : x ∈ A := by rw [hAx]; simp
    have hymem : y ∈ C := by rw [hCy]; simp
    have hx : block x = u := (Finset.mem_filter.mp hxmem).2
    have hy : block y = u+2 := (Finset.mem_filter.mp hymem).2
    have huniqueX := p3SingletonFiber_global_unique block u hA1 x hx
    have huniqueY := p3SingletonFiber_global_unique block (u+2) hC1 y hy
    have hmid :
        (Finset.univ.filter
          (fun z : Fin N => block z = block x+1)).card = 2 := by
      simpa only [hx] using hB2
    have hstep : block y = block x + 2 := by omega
    have hgap := p3Monotone_singletonDoubleSingleton_oppositeParity
      block hmono x y hstep huniqueX huniqueY hmid
    refine ⟨x,y,hgap.2,Or.inl hx,Or.inr (Or.inr hy),?_,?_⟩
    · exact huniqueX
    · exact huniqueY

end Hypertournaments
