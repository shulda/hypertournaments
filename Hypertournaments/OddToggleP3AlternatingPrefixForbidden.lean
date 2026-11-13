import Hypertournaments.OddToggleP3AlternatingInteriorOdd
import Hypertournaments.OddToggleP3RawAlternatingObstruction
import Hypertournaments.OddToggleP3SwitchingParity

/-!
# Genuine switching parity forces the missing p3 alternating endpoint

The true canonical parent order in the p3 construction is
  OLD_0 < ... < OLD_(m-1) < leftNew < rightNew,
with m=4k+2 and n=4k+3.

For any intrinsic switching-admissible E, if the first m
raw facet orientations of an increasing parent packet form
an alternating word of initial phase b, and the facet obtained
by deleting leftNew (the next index m) has raw sign b,
then switching parity forces the final raw facet sign to be !b.

The ENTIRE actual parent packet consequently has homogeneous
local type zero and is excluded by toggleZero. This uses no
random variables, source model or hidden preferred completion;
the remaining bridge is to interpret the actual selected source
patterns as exactly the first m raw signs and right endpoint.
-/

namespace Hypertournaments

/-- On any genuine switching packet of arity 4k+3, an
alternating prefix of length m=4k+2 and the correct
right-side endpoint beta at deletion position m together
force the forbidden homogeneous local packet. -/
theorem Hyper.p3Switching_alternating_prefix_right_forbidden
    (k a : ℕ) (E : Hyper (4*k+3) (Fin a))
    (f : Fin (4*k+4) ↪o Fin a)
    (hSwitch : localIndex E f.toEmbedding ∈
      switchingAllowed (4*k+3))
    (phase : Bool)
    (hInterior : ∀ i : Fin (4*k+2),
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
        p3AlternatingWord (4*k+2) phase i)
    (hBeta :
      E.orient (facet f.toEmbedding
        ((Fin.last (4*k+2)).castSucc)) = phase) :
    localIndex E f.toEmbedding ∉
      toggleZero (switchingAllowed (4*k+3)) := by
  classical
  let raw : Fin (4*k+4) → Bool :=
    fun i => E.orient (facet f.toEmbedding i)
  have hParentParity :
      (∑ j : Fin (4*k+4), p1BitToZMod (raw j)) = 0 := by
    have hCount :=
      (E.p3SwitchingAllowed_iff_rawFacetParityEven
        k f.toEmbedding).mp hSwitch
    have hCast := p1BoolPacketPositiveCount_toZMod raw
    exact hCast.symm.trans hCount
  have hPrefixParity :
      (∑ i : Fin (4*k+2),
        p1BitToZMod (raw (i.castSucc.castSucc))) = 1 := by
    calc
      (∑ i : Fin (4*k+2),
        p1BitToZMod (raw (i.castSucc.castSucc))) =
        ∑ i : Fin (4*k+2),
          p1BitToZMod (p3AlternatingWord (4*k+2) phase i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact congrArg p1BitToZMod (hInterior i)
      _ = 1 := p3AlternatingInterior_ZModSum_one k phase
  have hSplit :
      (∑ j : Fin (4*k+4), p1BitToZMod (raw j)) =
      (∑ i : Fin (4*k+2),
        p1BitToZMod (raw (i.castSucc.castSucc))) +
      p1BitToZMod (raw ((Fin.last (4*k+2)).castSucc)) +
      p1BitToZMod (raw (Fin.last ((4*k+2)+1))) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hSum :
      (1 : ZMod 2) +
      p1BitToZMod (raw ((Fin.last (4*k+2)).castSucc)) +
      p1BitToZMod (raw (Fin.last ((4*k+2)+1))) = 0 := by
    rw [hSplit, hPrefixParity] at hParentParity
    exact hParentParity
  have hLast :
      raw (Fin.last ((4*k+2)+1)) = !phase := by
    have hAlgebra : ∀ b c : Bool,
        ((1 : ZMod 2) + p1BitToZMod b +
          p1BitToZMod c = 0) ↔ c = !b := by decide
    have hBetaRaw :
        raw ((Fin.last (4*k+2)).castSucc) = phase := hBeta
    have hSum' :
        (1 : ZMod 2) + p1BitToZMod phase +
          p1BitToZMod (raw (Fin.last ((4*k+2)+1))) = 0 := by
      simpa only [hBetaRaw] using hSum
    exact (hAlgebra phase
      (raw (Fin.last ((4*k+2)+1)))).mp hSum'
  have hRaw : ∀ i : Fin (4*k+4),
      E.orient (facet f.toEmbedding i) =
        p3AlternatingWord (4*k+4) phase i := by
    intro i
    rcases i.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
    · rcases j.eq_castSucc_or_eq_last with ⟨z,rfl⟩ | rfl
      · simpa only [raw, p3AlternatingWord, Fin.val_castSucc] using
          (hInterior z)
      · have heven : (4*k+2)%2=0 := by omega
        simpa [raw, p3AlternatingWord, heven] using hBeta
    · have hodd : (4*k+3)%2≠0 := by omega
      simpa [raw, p3AlternatingWord, hodd] using hLast
  exact E.raw_alternating_not_p3ToggleAllowed k
    f.toEmbedding phase hRaw

end Hypertournaments
