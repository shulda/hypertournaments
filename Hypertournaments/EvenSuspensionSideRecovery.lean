import Hypertournaments.EvenSuspensionRecovery
import Hypertournaments.TwoPadOrdinaryAPTransfer

/-!
# Even suspension: exact source recovery on both canonical sides

The generic ordinary AP reflection isolates the assumption
CanonicalTwoPadSideRecovery: both higher source-side orientations
must recover their lower source-side n-orientations on all two-pad
tuples, for every ordered pad pair.

For the concrete even-suspension sign tables this follows directly
from the all-tuple theorem evenSuspension_orient_twoPads, since the
generic even old/pad injections are identical to the existing
canonical side embeddings. There is no sign reversal, auxiliary
amalgam order, or assumption about a source witness.

The other suspension obligations (membership in the raised age
and common-base preservation) remain separate.
-/

namespace Hypertournaments

/-- The two higher-arity even suspensions recover exactly both old
one-point source orientations, uniformly in all n, m and a. -/
theorem canonical_twoPad_recovery_evenSuspension
    {n a m : ℕ}
    (L R : Hyper n (Fin (a + 1))) :
    CanonicalTwoPadSideRecovery n a m L R
      (L.evenSuspension m (a + 1))
      (R.evenSuspension m (a + 1)) := by
  constructor
  · intro x y hxy t
    change (L.evenSuspension m (a + 1)).orient
      (evenPaddedTuple m (a + 1) x y hxy t) = L.orient t
    exact evenSuspension_orient_twoPads m (a + 1) L x y hxy t
  · intro x y hxy t
    change (R.evenSuspension m (a + 1)).orient
      (evenPaddedTuple m (a + 1) x y hxy t) = R.orient t
    exact evenSuspension_orient_twoPads m (a + 1) R x y hxy t

end Hypertournaments
