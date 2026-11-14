# Independent five-vertex catalogue review, 2026-11-14

Accepted for the exported encoding, signed permutation invariance, and complete
isomorphism-recognition statements. No blocking mathematical or Lean API issue
was found in the six reviewed modules.

The reviewer did not author or edit any of `Catalogue.lean`,
`CatalogueEncoding.lean`, `CatalogueAction.lean`, `CatalogueInvariant.lean`,
`CatalogueRecognition.lean`, or `CatalogueIsomorphism.lean`. The reviewer did
author their dependency `Mask.lean`; that module is explicitly excluded from
this independent-review claim and needs separate review.

## Source and representation

The source is the July five-constrained ternary classification supplement,
archive SHA-256
`d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3`.
The catalogue uses the twelve representatives
`0,1,2,9,10,11,12,13,25,41,82,83` and lexicographic triples
`012,013,014,023,024,034,123,124,134,234`, least significant bit first.
Each bit is interpreted literally as the Boolean value of the actual
intrinsic `Hyper.orient` on that increasing tuple.

The newer user-supplied November technical note reverses the prose convention
for positive versus negative increasing signs. The reviewed code fixes its
Boolean convention directly; it does not identify a bit with two contrary
sign conventions. Matching an individual labelled configuration to that note
therefore requires the stated convention change. Global reversal permutes
the two chiral pairs of type labels, while the five positive class palettes
are invariant as a list. The formal recognition theorems themselves use
actual orientations and contain no external sign-convention assumption.

## Actual encoding and recovery

`CatalogueEncoding` supplies ten genuine increasing tuple embeddings
`triple5`. Their coordinate bounds and strict inequalities are checked
finitely, and `triple5_complete` proves that every increasing three-tuple
appears. `encode5` packs the original structure's values on these tuples.

`encode5_bit` reads each original orientation exactly. `encode5_lt` bounds
the resulting natural by 1024. `maskHyper_encode5` then uses completeness
and the intrinsic preservation criterion to recover every injective ordered
tuple, including every odd permutation of the canonical tuples. This is
not merely agreement on an unordered support. In the other direction,
`encode5_maskHyper` recovers every input in `Fin 1024` exactly. Its bounded
input is necessary: higher mask bits are intentionally ignored by the
five-vertex presentation.

## Signed relabelling and invariance

`relabel5 m sigma` is defined as encoding the actual pullback of
`maskHyper 5 m` by the vertex permutation `sigma`. Thus the action cannot
silently omit the orientation sign of a relabelled triple.
`relabel5_orient` and `relabel5_mul` verify the action at the level of all
intrinsic tuples, with the correct multiplication order for pullbacks.

`CatalogueAction` checks preservation of `type5` by each of the four
adjacent transpositions on all 1024 masks. Its 32 chunks cover exactly the
blocks `32*c+k`, with `c,k : Fin 32`; the final division/remainder argument
covers all inputs. Every chunk is proved by ordinary kernel reduction.

`CatalogueInvariant` closes the invariance property under multiplication
and the identity in a genuine submonoid of `Equiv.Perm (Fin 5)`. Mathlib's
`Equiv.Perm.mclosure_swap_castSucc_succ` supplies generation of the full
symmetric group. Consequently `type5_relabel5` covers every vertex
permutation, rather than only the tested generators or even permutations.
`type5_encode5_preserves` transports this fact to arbitrary actual
orientation-preserving bijections of the original `Hyper` structures.

## Complete isomorphism recognition

`CatalogueRecognition` gives an explicit map on the five vertices for each
raw packet. The finite check proves both injectivity of that actual map
and the ten required signed orientation equalities. Injectivity on this
finite carrier supplies a bijection; `orbitWitnessPerm` uses choice only
to present its inverse. `orbitWitness_preserves` upgrades the checked
canonical tuples to preservation on all tuples.

`exists_representative` therefore proves that every actual intrinsic
five-vertex object is isomorphic to its assigned representative.
`representative_iso_iff_type5` proves both directions of recognition using
the same original `Preserves` relation. Invariance rules out accidental
identification of distinct labels; representative recovery and the explicit
witnesses prove existence. `representative_iso_iff` proves that the twelve
named entries are pairwise nonisomorphic. No source instance, bijectivity
hypothesis, or classifier-correctness premise remains exposed.

## Checked data and scope boundaries

The balanced lookup tree is executable data. Its correctness does not depend
on trusting the generator: the kernel-checked generator invariance and
explicit complete witnesses establish its actual isomorphism meaning.

As an additional independent check, the reviewer parsed both balanced Lean
trees directly and reconstructed the signed permutation orbits in a separate
Python program. All 1024 labels agree with these orbits; all 1024 decoded
vertex maps are actual permutations carrying the named representative to
the corresponding packet. The stated representatives are also the least
integers in those independently reconstructed orbits. The independent
four-support calculation agrees with the literal `support4` data.

The six reviewed modules do **not** export the semantic theorem identifying
`support4` with the original four-vertex `localIndex` restrictions. That
bridge must be supplied separately before this data table is used in class
normalization. Likewise, leastness and orbit-cardinality metadata are not
Lean theorem exports here; the exported mathematical classification is
exactly the complete list of twelve actual isomorphism types. These
boundaries do not weaken the isomorphism-recognition statements above.

## Validation and frozen sources

The author completed the catalogue target build, including all finite
recognition chunks. The reviewer used the resulting oleans for a separate
standalone check that instantiated all-tuple recovery, arbitrary-permutation
invariance, and the full actual-isomorphism iff without extra assumptions.
Eight endpoint axiom prints, including both recognition directions and the
explicit witness theorem, contained only
`propext`, `Classical.choice`, and `Quot.sound`.

The standalone source is
`../preparation/CatalogueIndependentReviewCheck.lean`; its log is
`../preparation/five-audit-run/catalogue-independent-endpoints.log`.
The independent parsed-source replay record is
`../preparation/five-audit-run/catalogue_independent_source_review.json`.
Project-wide rehashed build, source/facade checks, and complete defining-module
audits are the integration obligation recorded separately.

| Module | Reviewed SHA-256 |
| --- | --- |
| `Catalogue.lean` | `11694f7de43b1834cc9a852cd6ad593f262ed026cdb892d7e0c0ba8289be2f86` |
| `CatalogueEncoding.lean` | `afbf3908bd4f8202c6f258d1bd505a35f952948227901032e15a95efa6c935ad` |
| `CatalogueAction.lean` | `c77273a7add11340dff52db15e1f6c0a1090e28882e8d41157cf61b515158f41` |
| `CatalogueInvariant.lean` | `31caf94c43d53134abbc32058403629e6b00d835afa49255c863620dc7000cc6` |
| `CatalogueRecognition.lean` | `8a37941470fe14fc7459cfdb05c1e0576e9652ad3a309729292912cd2825bc21` |
| `CatalogueIsomorphism.lean` | `35819c55fb798e9e76ba3c2152ddbc2c5c41714779e336ac283c1be905f6ecb6` |
