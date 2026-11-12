import Hypertournaments.OddToggleP3MonotoneIsolatedBlocks
import Hypertournaments.OddToggleP3SixEdgeIsolatedWitnesses

/-!
# Six repeated-edge flags produce two globally singleton block labels

In a monotone word of old block labels of length at least seven,
a repeated-edge Boolean flag records whether each of the first
six consecutive pairs has the same label. At most two repeated
edges imply, by the certified six-edge parity selector, that
an even and an odd among the first six vertex positions have
both immediate incident edges strict. Monotonicity then makes
their labels unique throughout the ENTIRE word, even outside
the first seven positions.

This closes the exact local-to-global transfer needed in the
q=m-1 one-fresh p3 side-packet argument, conditional only on the
two repeated-edge bound. The remaining link from actual packet
occupancy to that repeated-edge bound is separate.
-/

namespace Hypertournaments

/-- Embed the six candidate positions into an actual sorted packet
with at least seven vertices. -/
def p3SixPosition (N : ℕ) (hN : 7 ≤ N)
    (i : Fin 6) : Fin N :=
  ⟨i.val, by have hi := i.isLt; omega⟩

/-- The successor of a candidate position also lies in the packet. -/
def p3SixSuccessor (N : ℕ) (hN : 7 ≤ N)
    (i : Fin 6) : Fin N :=
  ⟨i.val+1, by have hi := i.isLt; omega⟩

/-- The six edge flags of a monotonically ordered packet. -/
def p3SixActualRepeatFlags
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ) :
    Fin 6 → Bool :=
  fun i => decide
    (block (p3SixPosition N hN i) =
      block (p3SixSuccessor N hN i))

/-- A good edge genuinely carries a strict increase of block label. -/
theorem p3SixActualRepeat_false_strict
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ)
    (hmono : Monotone block) (i : Fin 6)
    (hgood : p3SixActualRepeatFlags hN block i = false) :
    block (p3SixPosition N hN i) <
      block (p3SixSuccessor N hN i) := by
  have hpos :
      p3SixPosition N hN i ≤ p3SixSuccessor N hN i := by
    change i.val ≤ i.val+1
    omega
  have hle := hmono hpos
  have hneq :
      block (p3SixPosition N hN i) ≠
        block (p3SixSuccessor N hN i) := by
    intro heq
    have htrue : p3SixActualRepeatFlags hN block i = true := by
      simp [p3SixActualRepeatFlags, heq]
    rw [hgood] at htrue
    cases htrue
  omega

/-- Every locally isolated candidate position of the certified
six-edge selector is the sole vertex of its label globally. -/
theorem p3SixActualIsolated_global_singleton
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ)
    (hmono : Monotone block) (i : Fin 6)
    (hiso : p3SixEdge_isolated_position
      (p3SixActualRepeatFlags hN block) i) :
    ∀ j : Fin N,
      block j = block (p3SixPosition N hN i) →
        j = p3SixPosition N hN i := by
  apply p3Monotone_isolated_of_strict_neighbors
    block hmono (p3SixPosition N hN i)
  · intro j hj
    rcases hiso.2 with hz | ⟨pred, hpred, hgood⟩
    · have hjval : j.val+1=i.val := hj
      have : False := by omega
      exact this.elim
    · have heq : j = p3SixPosition N hN pred := by
        apply Fin.ext
        have hv : j.val+1=i.val := hj
        change j.val = pred.val
        omega
      subst j
      have hstrict :=
        p3SixActualRepeat_false_strict hN block hmono pred hgood
      have hsucc :
          p3SixSuccessor N hN pred =
            p3SixPosition N hN i := by
        apply Fin.ext
        exact hpred
      rw [hsucc] at hstrict
      exact hstrict
  · intro j hj
    have heq : j = p3SixSuccessor N hN i := by
      apply Fin.ext
      change j.val = i.val+1
      have hv : (p3SixPosition N hN i).val+1=j.val := hj
      change i.val+1=j.val at hv
      omega
    subst j
    exact p3SixActualRepeat_false_strict
      hN block hmono i hiso.1

/-- At most two repeated adjacent edges among the first six
force globally singleton block vertices of both parities. -/
theorem p3SixRepeat_global_oppositeParity_singletons
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ)
    (hmono : Monotone block)
    (hbad : (Finset.univ.filter
      (fun i : Fin 6 => p3SixActualRepeatFlags hN block i = true)).card ≤ 2) :
    ∃ x y : Fin N,
      x.val%2=0 ∧ y.val%2=1 ∧
      (∀ z : Fin N, block z = block x → z=x) ∧
      (∀ z : Fin N, block z = block y → z=y) := by
  obtain ⟨i,j,hi,hj,hIi,hIj⟩ :=
    p3SixEdge_isolated_even_odd_witnesses
      (p3SixActualRepeatFlags hN block) hbad
  let x : Fin N := p3SixPosition N hN i
  let y : Fin N := p3SixPosition N hN j
  have hx : x.val%2=0 := hi
  have hy : y.val%2=1 := hj
  refine ⟨x,y,hx,hy,?_,?_⟩
  · exact p3SixActualIsolated_global_singleton hN block hmono i hIi
  · exact p3SixActualIsolated_global_singleton hN block hmono j hIj

end Hypertournaments
