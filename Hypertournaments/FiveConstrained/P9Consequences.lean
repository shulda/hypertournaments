import Hypertournaments.FiveConstrained.P9
import Hypertournaments.PairAmalgamation
import Hypertournaments.PairRamsey
import Hypertournaments.PairOrdering

/-!
# Actual amalgamation, Ramsey and ordering for the `P9` omission class

The finite calculation `p9_pairCancelling` discharges the sole forbidden
structure hypothesis of the existing general completion results.
-/

universe v w

namespace Hypertournaments.FiveConstrained

open StructuralRamsey
open StructuralRamsey.Structure

/-- Strong amalgamation in the original intrinsic omission language. -/
theorem p9_hasStrongAmalgamation : HasStrongAmalgamation p9Family :=
  pair_cancelling_hasStrongAmalgamation (by decide)
    p9Family p9Family_pairCancelling

/-- The witness retains the given side injections and their exact overlap. -/
theorem p9_strong_span
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper 3 A) (BB : Hyper 3 B) (CC : Hyper 3 C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Omits p9Family BB) (hC : Omits p9Family CC) :
    ∃ D : Hyper 3 (FiniteStrongSpan.Carrier f g),
      Omits p9Family D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) :=
  pair_cancelling_strong_span (by decide) p9Family p9Family_pairCancelling
    AA BB CC f g hAB hAC hB hC

/-- The class with a freely chosen linear order is actually Ramsey. -/
theorem p9_ordered_ramsey :
    CCO.UnaryHN.Native.Ramsey.{0,v,w} (Ramsey.orderedOmissionClass.{v} p9Family) :=
  Ramsey.pair_cancelling_ordered_ramsey (by decide)
    p9Family p9Family_pairCancelling

/-- Concrete finite Ramsey witnesses in the original hypertournament language. -/
theorem exists_p9_ordered_ramsey_witness
    {V W : Type v} [Finite V] [Finite W]
    (A : Hyper 3 V) (B : Hyper 3 W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (hA : Omits p9Family A) (hB : Omits p9Family B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper 3 X) (order : LinearOrder X),
      Omits p9Family D ∧ Structure.Arrow (Ramsey.toOrderedNative A orderA)
        (Ramsey.toOrderedNative B orderB) (Ramsey.toOrderedNative D order) κ :=
  Ramsey.exists_ordered_ramsey_witness (by decide) p9Family p9Family_pairCancelling
    A B orderA orderB hA hB κ

/-- One finite target works for every subsequently chosen pair of free orders. -/
theorem p9_ordering_property
    {V : Type} [Finite V] (A : Hyper 3 V) (hA : Omits p9Family A) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper 3 W), Omits p9Family B ∧
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (Ramsey.toOrderedNative A orderA)
          (Ramsey.toOrderedNative B orderB)) :=
  Ramsey.pair_cancelling_ordering_property (by decide)
    p9Family p9Family_pairCancelling A hA

end Hypertournaments.FiveConstrained
