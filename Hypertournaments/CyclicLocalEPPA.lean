import Hypertournaments.CyclicEPPA
import Hypertournaments.CyclicLocalType
import Hypertournaments.LocalForbiddenFamily

/-!
# The central ternary palette has no EPPA

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the finite cyclic-order discussion following `cor:even-no-eppa`.
The local-index and intrinsic circular-order presentations define the
same class, including structures with fewer than four vertices.
-/

namespace Hypertournaments

/-- The central-only ternary omission class is exactly the cyclic-order class. -/
theorem cyclicOrderClass_eq_omissionClass :
    cyclicOrderClass = omissionClass (localForbiddenFamily 3 ({2} : Set ℕ)) := by
  funext m
  apply Set.ext
  intro A
  change A.IsCyclicOrder ↔ Omits (localForbiddenFamily 3 ({2} : Set ℕ)) A
  exact (A.admissible_two_iff_isCyclicOrder).symm.trans
    (omits_localForbiddenFamily_iff_admissible ({2} : Set ℕ) A).symm

/-- Ordinary EPPA is identical in the circular and local-index presentations. -/
theorem cyclicOrderClass_hasEPPA_iff :
    ClassHasEPPA cyclicOrderClass ↔ HasEPPA (localForbiddenFamily 3 ({2} : Set ℕ)) := by
  rw [cyclicOrderClass_eq_omissionClass]
  exact omissionClass_hasEPPA_iff _

theorem cyclicOrderClass_not_hasEPPA_iff :
    (¬ ClassHasEPPA cyclicOrderClass) ↔
      ¬ HasEPPA (localForbiddenFamily 3 ({2} : Set ℕ)) :=
  not_congr cyclicOrderClass_hasEPPA_iff

/-- Finite cyclic orders fail ordinary EPPA in the central-only palette interface. -/
theorem cyclic_local_not_hasEPPA :
    ¬ HasEPPA (localForbiddenFamily 3 ({2} : Set ℕ)) :=
  cyclicOrderClass_not_hasEPPA_iff.mp cyclicOrderClass_not_hasEPPA

end Hypertournaments
