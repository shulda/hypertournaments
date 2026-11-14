# Independent review: binary orders and strong amalgamation

Reviewer: root agent, independent of the author of these two modules.
Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, small-arity clause of
`thm:constrained-classification`.

## Frozen inputs

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/BinaryOrder.lean` | `2b6a1a88e146b1fdea417bc213e381cce656a2034939ddf5f0f650635be242e6` |
| `Hypertournaments/BinaryAmalgamation.lean` | `c3e0dbfe31c3608979ffb9afca483397ae236326835aa3c689926add51b5d2df` |

## Mathematical and API checks

`binaryLT` reads the actual orientation on the ordered pair. It requires
distinct endpoints and does not use an ambient vertex order. The swap law
gives asymmetry and comparison in one of the two directions. The pair
embedding agrees with every actual injective two-tuple.

For three distinct vertices, a failure of transitivity with the two forward
successive edges makes the three normalized facet bits constant. The
existing zero-index characterization excludes this under palette `{1}`.
In the reverse direction, both possible constant packets give a directed
cycle, with the all-true case explicitly using the reversed relation.
The index bound excludes any remaining index other than one. Thus the iff
is exact and holds on arbitrary, including infinite and empty, carriers.

The recovered `LinearOrder` has strict relation definitionally `binaryLT`.
The standard constant-sign model is shown to recover this order on every
ordered pair, rather than just on increasing pairs. Consequently the
embedding iff concerns the original `Preserves` relation and precisely
strict monotonicity between the reconstructed orders.

The amalgamation theorem infers finiteness of the base from its given
injection. It derives the base's admissibility by restriction, turns the
original preserving injections into increasing ones, and applies the
existing exact-overlap shuffle. It does not replace the given injections
or impose a compatibility premise. The two side models are recovered on
all tuples and embed into the constant-sign target. The target is admissible
for `{1}`. Its carrier and injections are the actual `FiniteStrongSpan`
objects, so the existing commute, overlap, and coverage theorems apply.
Empty bases and empty sides are included without an existence-of-root step.

## Independent verification

Rebuilt `Hypertournaments.BinaryAmalgamation` successfully: 1516 jobs.
Printed axiom dependencies for the transitivity iff, reconstructed order,
embedding iff, and final strong-span theorem. Every print uses only
`propext`, `Classical.choice`, and `Quot.sound`.

No mathematical gap, extra source assumption, or surrogate embedding
interface was found. The final package also receives the complete source,
kernel, and defining-module audits recorded in its verification receipt.
