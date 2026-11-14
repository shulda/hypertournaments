# Five-constrained ternary classification, 2026-11-14

## Sources and formulation

The user authorized the complete five-constrained ternary classification on
2026-11-14, after the mathematical article and general affine potential
section were completed. The continuum/Fraisse corollary remains excluded.

The original July classification supplement is
`amalgamation_five_constrained_3_hypertournaments_supplement(2).zip`, SHA-256
`d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3`.
Its paper source has SHA-256
`126f6110d58e2bc0824f981289dfcad890b8edea5f9e0b3293377d9c4b6f74f4`.
The later uploaded note `hypertournament_negative_ap_v2_final.tex` has SHA-256
`a06eb1ae0377e798491354faa95357501046f79c5eaa2d482adcfeef02d412d7`.
The main article pin remains
`919349e7eceed3c7fa0ed126a337c6fae6624704`.

The July paper imposes separate four- and five-vertex conditions and proves
their normalization in unbounded AP classes. The November note's negative
theorem imposes only five-vertex conditions. These differ on small carriers:
five-vertex conditions alone admit every four-vertex structure. Consequently
the five surviving palettes are positive AP/SAP classes in the normalized
four/five presentation; their names are not literal equalities of the
five-only classes on small carriers.

The July bit one denotes the positive increasing orientation, while the
November note uses bit zero. The formal mask is simply the literal Boolean
value of `Hyper.orient` on an increasing triple. Changing this global
convention exchanges catalogue types 3/7 and 10/11; the five positive
palettes are invariant under that exchange. Vertex relabelling always uses
the actual alternating `Hyper` law.

## Finite negative proof

The twelve canonical masks are
`0,1,2,9,10,11,12,13,25,41,82,83`. Their four-support masks are
`4,6,6,7,6,6,6,7,5,7,3,3`, with bits 0,1,2 denoting the original local
indices H4,O4,C4.

The original 2048-row candidate table was independently replayed from its
definitions. All 2043 negative rows pass; the retained diagrams number 219.
A greedy selection of 37 of these diagrams covers exactly the 2043 negative
palettes. No optimality claim is needed. An additional independent audit
recognizes isomorphism by relabelling the full cyclic ternary relation,
rather than by the parity formula or the generated type lookup. It confirms
the same 37-diagram cover and the same five survivors.

The November note uses a 42-diagram library over bases of size at least
four and a separate bounded-extension/JEP proof for palettes 1025 and 2049.
Both exceptional palettes already have the ordinary one-point obstruction
`(baseSize, base, left, right) = (3,0,1,0)` in the literal Boolean convention.
Its two sides have four-types O4 and C4 and unequal links. Its eight completed
five-types are `2,3,4,5,6,7,2,1`, so none is P0,P10,or P11. The formalization
uses this smaller unified proof. The larger extension catalogues are not
required by the classification.

The checker's soundness has three separate semantic steps:

1. The side and mixed packets compute the actual local indices and the actual
   five-vertex isomorphism labels.
2. Every hypothetical distinct-point amalgam restricts to the canonical
   union. Its mixed orientation bits reconstruct all intrinsic orientations.
3. Unequal bounded link masks give a genuine differing orientation, excluding
   identification of the two new points. Thus the result rules out ordinary
   AP in arbitrarily large targets.

## Positive and normalization proofs

The palettes `1,119,257,4095` are identified with the existing cyclic,
H4-free, even, and unrestricted ternary classes. Palette 3583 is identified
with omission of the concrete P9 mask 41. Its actual pair-cancellation proof
instantiates the already proved strong amalgamation, native ordered Ramsey,
and full ordering theorems.

The class interface retains separate four/five predicates. Hereditary AP
gives JEP; JEP and actual unboundedness extend every admitted four-point
member to five points. Together with consistency this proves normalization
on every realized four-type. Pure ordered finite Ramsey, with no Ramsey
assumption about the constrained class, proves that unboundedness is exactly
admission of C4 and P0, or just P0 in the normalized presentation.

## Implementation and verification

Implementation is in `Hypertournaments/FiveConstrained/` and the shared
`FiniteClassAmalgamation.lean`. The existing `Hyper`, `Preserves`, `HasAP`,
local-index, cochain, and immutable Ramsey vendor APIs are preserved.

Finite facts are checked by kernel reduction. Balanced executable lookups
and small reflection modules keep resource use bounded. The source arrays,
signed action, explicit orbit witnesses, exact profiles and coverage remain
reproducible from the retained data and generators in `tools/five_constrained`.

The complete rehashed local build passed with 2223 jobs. Source guards cover
512 project modules (511 in the facade), 94 specific external Mathlib roots
and the unchanged 119-module Ramsey vendor closure. Both standalone
regenerators pass `--check`, and all ten source-guard regression tests pass.

The complete defining-module audits passed for 5245 Hypertournaments,
117 CCO, 1700 PartiteConstruction and 805 SuccessorTree declarations, a total
of 7867. The allowed axioms are exactly `propext`, `Classical.choice` and
`Quot.sound`; no custom or native proof axiom is used. Readable endpoint
checks also passed.

Independent reviews, with frozen source hashes, are:

- `FIVE_CATALOGUE_REVIEW_2026-11-14.md`;
- `FIVE_MASK_REVIEW_2026-11-14.md`;
- `FIVE_MASK_AND_POSITIVE_REVIEW_2026-11-14.md`;
- `FIVE_CONSTRAINED_CLASS_AND_CERTIFICATE_REVIEW_2026-11-14.md`.

The verification receipt is `verification/five_constrained_2026-11-14.json`.
Exact proposed-head and merged-head CI evidence belongs in the integration
pull request; source/configuration bindings are retained in the receipt.
