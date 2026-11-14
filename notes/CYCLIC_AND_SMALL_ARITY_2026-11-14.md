# Cyclic orders and the small-arity classification

Article source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`.
Parent main: `ffab0bdb92d9e8134928799b29316e437698098a` (PR #414).

This package proves the small-arity clause of
`thm:constrained-classification`, the finite cyclic-order non-EPPA argument
following `cor:even-no-eppa`, and the compatible linear-order Ramsey and
expansion claims for cyclic orders in the introduction. All use the shared
intrinsic `Hyper`, `Preserves`, actual local index, and finite witness APIs.
No theorem from the postponed five-constrained ternary classification is used.

## Exact small-arity classes

The central type is equivalent to unboundedness by the previously proved
finite Ramsey argument. Valid central palettes are exactly:

| Arity | Allowed indices | Class | Strong-amalgamation provider |
| --- | --- | --- | --- |
| 2 | `{1}` | Transitive tournaments / linear orders | `binary_transitive_strong_span` |
| 2 | `{0,1}` | All tournaments | Existing `unrestricted_strong_span` |
| 3 | `{2}` | Cyclic orders | `cyclic_strong_span` |
| 3 | `{0,2}` | Even ternary orientations | Existing `switching_strong_span` |
| 3 | `{1,2}` | H4-free ternary orientations | Existing `central_next_strong_span` |
| 3 | `{0,1,2}` | All ternary orientations | Existing `central_next_strong_span` |

`SmallArityPalettes` proves the two/four exhaustive palette equalities.
`SmallArityClassification` produces actual strong amalgams for every row
on the original `FiniteStrongSpan.Carrier f g`, keeping the source injections.
These constructions need only finite side carriers; source finiteness and
admissibility are inferred. Empty bases and empty sides are included.

The combined result is:

```lean
unbounded_hasAP_iff_hasStrongAmalgamation
    (hn : 2 ≤ n) (S : Set ℕ) (hU : UnboundedAdmissible n S) :
    HasAP n S ↔ HasStrongAmalgamation (localForbiddenFamily n S)
```

This iff has no validity assumption: impossible indices in `S` are removed
internally using `admissible_validize` and `hasAP_validize`. The actual
arbitrary-finite-carrier theorem is `strong_span_of_hasAP_all_arities`.
The high-arity negative theorem is used only after all its premises have
been supplied for the internally normalized palette.

For valid palettes, `amalgamation_classification_all_arities` proves

```lean
HasAP n S ↔ n ≤ 3 ∨ NecessaryAlternatives n S
```

under `2 ≤ n` and central membership. Its unboundedness-premise variant
is `unbounded_amalgamation_classification_all_arities`.

## Intrinsic reconstruction and cuts

`BinaryOrder` reads the forward orientation of a pair without any ambient
order. The forbidden zero-index packet is exactly a directed triangle, giving
the full iff between `{1}`-admissibility and transitivity. The resulting
linear order is on the original carrier, including infinite and empty ones.
`Preserves` is equivalent to strict monotonicity between the recovered orders.

`CircularHyper` encodes Mathlib's actual `CircularOrder`; false orientation
corresponds to strict circular betweenness. `IsCyclicOrder` existentially
hides the presentation. `CyclicRelation` constructs that circular order
directly from `{2}`-admissibility: the required transitivity is forced by
one four-vertex packet, and all repeated-vertex weak-betweenness cases are
checked. `CyclicLocalType` proves the converse, hence

```lean
Hyper.admissible_two_iff_isCyclicOrder (A : Hyper 3 V) :
    Admissible {2} A ↔ A.IsCyclicOrder
```

for every carrier without finiteness or nonemptiness assumptions.

`CircularCut` puts a chosen root first in a linear order on the entire
carrier. Circularizing the cut recovers every ternary relation, including
repeated points. Root-preserving circular embeddings are increasing in the
cut orders. `CyclicAmalgamation` uses common-root cuts for a nonempty base
and independent cuts for an empty base. The previously proved finite-order
shuffle then closes into a circle on the exact original union carrier.

## Shorter finite cyclic EPPA proof

The manuscript's rotation-group argument is replaced by one partial map.
On three distinct source vertices `a,b,c`, the map `{a,b} -> {a,c}` fixes
`a` and maps `b` to `c`. Two-point ternary structures have no tuples, so
both copies are genuinely isomorphic induced substructures.

An extending automorphism of a finite cyclic target fixes the image of `a`.
In the cut at that point it is increasing, hence identity by the existing
finite-order theorem `StrictMono.apply_eq`. This contradicts its prescribed
image of `b`. Target finiteness comes from the actual EPPA witness itself.

`CyclicEPPA` proves this target-specific obstruction for every source with
three distinct vertices and then gives the concrete `Fin 3` cyclic example.
`CyclicLocalEPPA` identifies the finite cyclic class with the original
`localForbiddenFamily 3 {2}` omission class, including small carriers, and
exports `cyclic_local_not_hasEPPA`.

The target is explicitly assumed cyclic throughout. These theorems make
no assertion ruling out unrestricted ternary EPPA witnesses.

## Compatible-order Ramsey and expansion properties

`CyclicRamsey` names both the original ternary orientation and a compatible
linear order in the existing native language. Forgetting and reconstructing
the orientation gives actual native embeddings to and from pure finite
linear orders. The already proved pinned pure-order Ramsey theorem therefore
gives `exists_cyclic_ramsey_witness` and the full native class theorem
`cyclic_expansions_ramsey`. All source/target instances are discharged.
The finite nonempty colour type may live in a separate universe.

For `CyclicExpansionProperty`, any two compatible linear presentations of
the same finite reduct are order-isomorphic by their finite ranks. Such an
isomorphism preserves all circular triples. Thus the expansion witness is
the source reduct itself, fixed before both compatible orders are selected.
The theorems quantify only over compatible orders, with this hypothesis
explicit in both the class and the embedding statements.

The existing exact 119-module Ramsey closure is unchanged at source
`48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6`, digest
`ae194b3154e25d52e71523b0b8eae966acb6f5c851dc94e2aed9c52ef1ab3422`.

## Independent reviews and validation

| Modules | Independent review |
| --- | --- |
| Binary reconstruction and SAP | `BINARY_ORDER_REVIEW_2026-11-14.md` |
| Circular encoding and cuts | `CIRCULAR_ENCODING_REVIEW_2026-11-14.md` |
| Intrinsic cyclic reconstruction and local-index iff | `CYCLIC_LOCAL_TYPE_REVIEW_2026-11-14.md` |
| Cyclic strong amalgamation | `CYCLIC_AMALGAMATION_REVIEW_2026-11-14.md` |
| Cyclic EPPA and omission-class bridge | `CYCLIC_EPPA_REVIEW_2026-11-14.md` |
| Exhaustive small palettes and all-arity AP/SAP | `SMALL_ARITY_CLASSIFICATION_REVIEW_2026-11-14.md` |
| Compatible-order Ramsey and expansion property | `CYCLIC_RAMSEY_REVIEW_2026-11-14.md` |

The package receipt `verification/cyclic_small_arity_2026-11-14.json` records
the full rehashed build, complete source/facade and immutable vendor checks,
source-guard regression tests, readable endpoint checks, four complete
defining-module axiom audits, and hashes of every source/configuration input.
The axiom allowlist is exactly `propext,Classical.choice,Quot.sound`.

## Remaining source obligations

The additional infinite pair-cancelling embedding antichain cited from
Sullivan Proposition 4.11 still needs a proof, and the resulting continuum
many countable homogeneous structures need a verified Fraisse existence
construction and relational adapter. These are separate from the finite
classification, Ramsey, amalgamation, and EPPA results above.
Five-constrained ternary classification remains postponed. Historical claims
and conjectures are not treated as completed theorem obligations.
