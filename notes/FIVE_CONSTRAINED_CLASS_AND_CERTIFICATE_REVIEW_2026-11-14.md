# Independent class and certificate review, 2026-11-14

Reviewed the original July five-constrained classification supplement
(`amalgamation_five_constrained_3_hypertournaments_supplement(2).zip`,
SHA-256 `d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3`)
and the uploaded November technical note
`hypertournament_negative_ap_v2_final.tex` (SHA-256
`a06eb1ae0377e798491354faa95357501046f79c5eaa2d482adcfeef02d412d7`), together with the modules bound
below. No blocking mathematical issue was found in these modules.

The reviewer implemented `P9.lean`, `P9Consequences.lean`, and
`CertificateStructures.lean`; those three modules are explicitly outside
this independent review. Their interfaces were read as dependencies, not
independently approved here. Compilation, the complete axiom audit and exact
proposed-head CI remain separate integration checks.

## Source formulations and the smaller certificate library

The July source uses separate four- and five-type palettes and normalizes
the former to the union of the latter's actual four-supports. The November
note defines its negative theorem using five-vertex constraints alone. On
carriers of size four those constraints are vacuous, so the two class
predicates must not be silently identified. `Classes.lean` preserves both
palettes independently; `Normalization.lean` proves when they agree.

The two sources also name the raw signs oppositely. The implementation
reads each mask bit literally as the Boolean value of `Hyper.orient` on
the corresponding increasing tuple. Complementing all ten bits exchanges
the named pairs P3/P7 and P10/P11, while preserving the five surviving
palettes as sets. No sign-name conversion is used as a proof assumption.

The November note's two JEP cases have simpler legitimate one-point
obstructions over a three-vertex base. For raw masks `(A,L,R)=(0,1,0)`,
the eight five-vertex completions have types
`2,3,4,5,6,7,2,1`, so none is admitted by palette 1025 or 2049.
Both sides are four-vertex structures;
their links differ. This explains why searching only bases of size at
least four unnecessarily separates those cases.

An independent replay reconstructed isomorphism types by relabelling the
**full cyclic ternary relation**, without using an inversion-parity formula
or the implementation's lookup table. It classified all 1024 five-vertex
masks and all 16 four-vertex masks, built the 37 retained diagrams, tested
every mixed assignment, and checked every odd palette below 4096. Exactly
2043 palettes were refuted. The survivors were exactly
`1,119,257,3583,4095`. Local evidence is
`../preparation/FiveConstrainedIndependentRelationReview.json`.

## Intrinsic semantics and normalization

`FiniteClass.HasAP` retains arbitrary orientation-preserving injections and
permits identifications outside the base. `HasSAP` adds the exact-overlap
condition. The omission-class SAP interface and old local-palette AP
interface are connected by definitional equivalences. The AP-to-JEP theorem
correctly assumes positive arity; the ternary instance discharges it.

`PacketAllowed` is defined by actual isomorphism to a representative.
`FiveAllowed` quantifies over every intrinsic five-tuple. Passing to
increasing presentations is justified by sorting and actual vertex
permutations; it does not introduce an order-preservation restriction on
the class embeddings.

The catalogue chain proves that encoding and decoding recover every tuple,
defines relabelling by actual pullback, proves invariance under adjacent
swaps and then all permutations, and supplies an injective representative
isomorphism for every raw mask. `representative_iso_iff_type5` therefore
recognizes genuine original structures rather than an assumed finite table.

Normalization uses AP-to-JEP and unboundedness to extend every admitted
four-vertex structure into an admitted five-vertex structure. The reverse
support inclusion correctly retains the explicit `Consistent` premise.
The equality is restricted to realized four-indices at most two, so phantom
high bits do not require a false literal equality of natural-number masks.

## Packet logic and ordinary non-amalgamation

`PacketSemantics` identifies the executable four-packet with the existing
intrinsic `localIndex`, and the literal ten-bit packet with the actual
five-vertex encoder. Arbitrary carrier injections are retained.

`CertificateLogic` proves that the bitwise requirement masks mean exactly
universal admission of the listed side and mixed restrictions. Fold
accumulators and repeated patterns are harmless set unions. The profile
contains every mixed assignment, not an assumed optimal or minimal list.

`CertificateSoundness` derives actual side membership from those conditions.
`CertificatePackets` identifies the actual side and mixed-joint restrictions
with the exact increasing four/five packets used by those conditions.
A hypothetical arbitrary finite ordinary amalgam restricts to the canonical
one-point union. Actual side orientation disagreement excludes identification
of the two new points. Recovering the mixed bits covers every intrinsic
orientation on that union, and the finite rejection contradicts its
membership. The generic theorem explicitly exposes actual disagreement;
the bounded-checker wrapper supplies it using proved link bounds and
unequal-link facts. `normalized_not_hasAP` discharges those bounds from the
actual 37-diagram library, so this is not an uninstantiated provider premise.

Ten focused independent Lean checks, including normalization, catalogue
recognition, packet interpretation and the bounded ordinary-AP checker,
reported only `propext`, `Classical.choice`, and `Quot.sound` (some use fewer).
The local log is `../preparation/FiveConstrainedIndependentClassAudit.log`.

## Literal generated data and proof coverage

The review parsed the actual retained `CertificatesData.lean`, rather than
checking only the historical JSON or rerunning its generator. Its 37 literal
diagrams exactly match both the compact July cover and the generator's
`DIAGRAMS`. Decoding the original July CSV also confirms that each is an exact
member of its 219 distinct retained diagrams. An independent implementation using full cyclic orientation
relations and vertex permutations recovered all 37 side requirements and
all 1328 mixed requirement rows exactly. The four-supports were independently
recovered from the actual representatives. Every retained diagram satisfies
the stated base-size, base-mask, link-mask and unequal-link bounds.

All 2048 literal choice entries were checked against those independently
computed requirements. Each of the 2043 negative palettes is blocked by its
chosen diagram; the five positive palettes are not blocked by any retained
diagram. The actual `certificateChoiceLookup` decision tree was separately
parsed and evaluated on all 2048 inputs and agrees with every literal choice
entry. Thus the optimized selector, not just the reference array, is covered.
Evidence is `../preparation/FiveConstrainedIndependentLeanLiteralReview.json`.

The generated proof files contain exactly 37 distinct profile equalities,
each proved by `rfl`, and 16 coverage facts, each proved by `rfl`. Their
128-element intervals cover exactly `0,...,2047`, with no gap. The top
profile theorem handles every `Fin 37` index. Array access uses actual bounds,
and the coverage assembly removes the selector's modulus using the actual
`Fin 2048` bound. The final coverage theorem adds the proved link inequality
to the exact computed profile; the separate numerical bounds are available
for intrinsic soundness. No external search or generator correctness is
assumed by these Lean facts. The generator's `--check` mode also passed its
byte-for-byte retained-source comparison.

## Classification endpoints

`Positive.lean` was independently reviewed as well. Its four familiar
palettes `1,119,257,4095` are identified with the actual local four-type
classes having masks `4,6,5,7`, respectively. The finite coverage facts
prove that every five-packet compatible with the four-condition is allowed;
the converse retains the original four-condition, including small carriers.
Palette `3583` excludes exactly type P9. Its packet-level equivalence uses
actual representative permutations, and its carrier-level equivalence
composes those permutations with arbitrary intrinsic injections. The
four-condition is correctly automatic in this case. SAP is transported
pointwise through these actual class equivalences and the existing
omission/local-class SAP interfaces. This review checks the aliases and
transport, while retaining the stated exclusion of the reviewer-authored
P9 proof modules themselves.

The unboundedness argument uses finite Ramsey only in the empty relational
language with an auxiliary linear order. It extracts an actual constant-sign
embedding of arbitrary fixed size. It assumes no Ramsey property of the
constrained class. Conversely, actual constant-sign structures give members
at every size. This proves unboundedness exactly when the separate palettes
contain C4 and P0, and exactly when P0 belongs to the normalized palette.

`Classification.lean` retains `palette < 4096` and actual unboundedness in
the complete normalized classification. All numerical diagram bounds in
the negative direction are discharged by the concrete library. The positive
direction uses actual SAP witnesses, so the resulting AP/SAP equivalence
does not confuse ordinary and strong amalgamation. The separate four/five
endpoint retains consistency, actual unboundedness, and normalization of
every realized four-type. The uploaded November convention is exposed as
`fiveOnlyClass`, with its five-palette condition explicitly vacuous on
smaller carriers. Its negative theorem exports only the necessary list of
five exceptions, without claiming their sufficiency in that convention.

After the frozen classification target compiled, 20 additional independent
endpoint checks imported `Classification.lean` and inspected the generated
profile/coverage facts, all classification endpoints, unboundedness and
actual side/mixed packet adapters. Every result used only the three allowed
standard axioms, or fewer. The log is
`../preparation/FiveConstrainedIndependentFinalEndpointAudit.log`.

The supplementary independent `Positive.lean` check imported that frozen
module and inspected all 11 exported alias/transport endpoints. Every result
used only the allowed standard axioms. Its log is
`../preparation/FiveConstrainedIndependentPositiveEndpointAudit.log`.

## Reviewed source hashes

Production sources were frozen after the successful classification build.
These hashes include every generated profile and coverage module; the generator
is recorded for reproducibility, and remains outside the Lean trust boundary.

| Module | SHA-256 |
| --- | --- |
| `FiniteClassAmalgamation.lean` | `2f49430c4ba6473db52038c1fe2647369262dfde96fa7367b3a5013b3b43f6b5` |
| `FiveConstrained/Classes.lean` | `7e3b31e3cedc3ce7beda268466e958457c7dc84ea3997bb6a0f2dbeb5ad6daf5` |
| `FiveConstrained/ClassRecognition.lean` | `c0a93a60cfb0b1f4f25e80d97cff2cb4b7eaf663cdc955990b006aa2a91aa42b` |
| `FiveConstrained/Normalization.lean` | `e309c21227c9fc449d666fdff682a7e01b9374fdadb989de2f86e3ef5a10441c` |
| `FiveConstrained/PacketSemantics.lean` | `2bb99dbb9e420e68d595ff883d6379fd387ffbd5d2932a2977432b54219b3187` |
| `FiveConstrained/CertificateLogic.lean` | `303928f2079d702334413cf3b9d6efd96c5cb7984130d54ce66a43dd078f78c2` |
| `FiveConstrained/CertificateSoundness.lean` | `835a50a5bc965a51ce0b396014b998d89a138f9dca78d86a91bbfa38aa4bdece` |
| `FiveConstrained/CatalogueEncoding.lean` | `afbf3908bd4f8202c6f258d1bd505a35f952948227901032e15a95efa6c935ad` |
| `FiveConstrained/CatalogueAction.lean` | `c77273a7add11340dff52db15e1f6c0a1090e28882e8d41157cf61b515158f41` |
| `FiveConstrained/CatalogueInvariant.lean` | `31caf94c43d53134abbc32058403629e6b00d835afa49255c863620dc7000cc6` |
| `FiveConstrained/CatalogueRecognition.lean` | `8a37941470fe14fc7459cfdb05c1e0576e9652ad3a309729292912cd2825bc21` |
| `FiveConstrained/CatalogueIsomorphism.lean` | `35819c55fb798e9e76ba3c2152ddbc2c5c41714779e336ac283c1be905f6ecb6` |
| `FiveConstrained/CertificatePackets.lean` | `bb2259e7bc5dbe96c991fef5a096fc45abb4d9008be94cadb68b5a119ed6eb2e` |
| `FiveConstrained/Classification.lean` | `345bf792c3fea4634173685ace575f88dd94e89138f775753d1b2b5c3be7d375` |
| `FiveConstrained/Positive.lean` | `a42e4faa6c7e742b6916f75411d9034d86b8e46f228c0e3e184fe77fc9536551` |
| `FiveConstrained/Unbounded.lean` | `595ed11dada09f80e7039ae38bbdd74c1dbc20b265b1eb6604c3be9967e3b646` |
| `FiveConstrained/RamseyHomogeneity.lean` | `6716d395de0f2b059a5c81af41adb912ad5124da117844f4e655283814be6bb2` |
| `FiveConstrained/CertificatesBasic.lean` | `cdc5b5c283c137dc4a52fc87e4151277e189c8c37d9289664a4ab1da18eeb904` |
| `FiveConstrained/CertificatesData.lean` | `6977ef76d7fb076dd46eff1f4c050e473faca4484de937eb09c22b7a1146a8cf` |
| `FiveConstrained/CertificatesProfiles.lean` | `bb8207e630134db6794d75181e1908534bb63ca716891ccf86a57eafab37746c` |
| `FiveConstrained/CertificatesProfiles0.lean` | `c6a28c22e9c224c481e0bc0984d56e644e9de5587fe8a0f8c74953999f9f0a03` |
| `FiveConstrained/CertificatesProfiles1.lean` | `aa2e5cf266a2d438f2a950ed707ea5c70659cedf2cecd1067756e8d428b26dfb` |
| `FiveConstrained/CertificatesProfiles2.lean` | `2920948f0a54d012602b5da86667afbe5528fab6067909523a741ef57f6ca0ea` |
| `FiveConstrained/CertificatesProfiles3.lean` | `60a8ba51a91b16e5c7c451df79b6d2ac7e403bc0532522e8a54093cc47b2c73f` |
| `FiveConstrained/CertificatesProfiles4.lean` | `aff932e640097dc15b1f31313810d1f46536aaf859957b9bd44ff7892978b267` |
| `FiveConstrained/CertificatesProfiles5.lean` | `c281690bd149ae2f2a7fc9b58c3751c9d10af346f2dbadd21b529a29ca51cc3c` |
| `FiveConstrained/CertificatesProfiles6.lean` | `a78bf0c797e80452a5d84edd009639379d521de9f630ab1ef71fa59c5169a05c` |
| `FiveConstrained/CertificatesProfiles7.lean` | `25b39667ab8d5aa9a4679f2d901bdffd94fa258a724b855c3c1df58460d01bea` |
| `FiveConstrained/CertificatesCoverage.lean` | `4e6e4574fb4ff3d3e5784f9ecb411847b14e59c72e235c72ff3876a3d4d97825` |
| `FiveConstrained/CertificatesCoverage0.lean` | `dcb8974998d085147dfd5ea0a84deaed811312d41bf37a1684111a2933426a8d` |
| `FiveConstrained/CertificatesCoverage1.lean` | `8daf240e32b377ee86406a1b641c9120f580f6b57165a683e6143f9cece19d45` |
| `FiveConstrained/CertificatesCoverage2.lean` | `b788c0dc2c908a63923b6d173c2f7b16085e15ee88f0bbe0c68a24d04734327a` |
| `FiveConstrained/CertificatesCoverage3.lean` | `8cd917424b26c283ccb0d8ca89b3ac3c008e4aaafbe3712ed56c5600562cd946` |
| `FiveConstrained/CertificatesCoverage4.lean` | `76bb14989adb18ac0e0fff5e7708932f0f693448b2c0af34d0eaa0083405dcf7` |
| `FiveConstrained/CertificatesCoverage5.lean` | `4a5b664bbcf20e855350dc1ff1fb7698114774e4131d390f6c62a7283955e635` |
| `FiveConstrained/CertificatesCoverage6.lean` | `14aad5f3e787c6ed61f55f7aa0c3aae4dc4107efc3a4b46afb93244391132506` |
| `FiveConstrained/CertificatesCoverage7.lean` | `db3ef5670ef9203929dffeb771c3f1bc5f2ceff0ab64819f238878eb7cb36435` |
| `FiveConstrained/CertificatesCoverage8.lean` | `46478041eb1d76fdfd916990336a6e81ac18a269306107cde79e3eb6a204dba3` |
| `FiveConstrained/CertificatesCoverage9.lean` | `a9ea7e6741a3078ef0cb9629dc20ff74f3753f7342edf2604b20eb44c58c94a7` |
| `FiveConstrained/CertificatesCoverage10.lean` | `5edb2620e0789ca929fefb7a654208179c22b328cacce91ee473b95036cf522c` |
| `FiveConstrained/CertificatesCoverage11.lean` | `d106dbbb9a32998fd1998b7f7037a288421d3f994e5677fd9dc7b219732eaa51` |
| `FiveConstrained/CertificatesCoverage12.lean` | `735d8a05ba1deb1c698fb4fd8af7ce5cd6a8b928ef8ca5646ba6e38ff170effd` |
| `FiveConstrained/CertificatesCoverage13.lean` | `5d79751a480fbbe7a339a1f5153e729a88dcdee616444e49ed2cbf018d7610f3` |
| `FiveConstrained/CertificatesCoverage14.lean` | `abd7d1c2e68da2716b6a8411092d001d19e4215b2b99fca4aeaa4623c3568247` |
| `FiveConstrained/CertificatesCoverage15.lean` | `62d62a0fe26e13af95035c0c9d7fb6eeeaf559dce9e2f7263f200585508e378a` |
| `tools/five_constrained/generate_certificates.py` | `aad4176f0cca6c77fc659d2b47f59bb29fdd8a611ee5af3297325f084e9b9538` |
