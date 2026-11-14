# Independent review of ordinary EPPA extension and Klein lifting

## Source and result

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`, together with the elementary quotient
lifting argument in the proof preparation. This review covers
`EPPAExtension.lean` and `EPPAKleinLift.lean`, authored separately from
this review. No blocking mathematical or API issue was found.

The main conclusion is an actual homomorphism from a Klein four-group
into the ambient automorphism group, extending a prescribed local action
on an embedded packet. Its construction needs only ordinary separate EPPA
extensions. It does not assume those extensions already form a homomorphism.

## Actual induced isomorphisms

`Hyper.PartialAutomorphism.betweenCopies` uses the literal subsets
`Set.range f` and `Set.range g` of the original vertex carrier. Its
equivalence is the inverse range equivalence of f followed by the range
equivalence of g. It sends the actual source vertex f(x) to g(x).

For every injective tuple of the source subset, the proof pulls its labels
back through f's range equivalence to a tuple in the common structure P.
The two supplied `Preserves` hypotheses then identify both ambient
orientations with P's orientation. This verifies the induced structures
on the entire source and target subsets, with no auxiliary order.
The ranges may overlap; no unnecessary disjointness assumption appears.

`extend_isomorphism` applies the existing ordinary witness field to this
one partial automorphism and recovers its value at every f(x). Thus it
provides one actual ambient automorphism for the whole induced isomorphism.
Different partial automorphisms still receive separate existential choices;
no coherence assumption is introduced.

## Fiber subgroup and the genuine odd kernel

`Hyper.packetExtensionGroup` is a subgroup of `B.Aut × E`, consisting of
pairs (g,a) whose actions agree on the embedded packet. Its multiplication
uses the actual permutation composition convention: the right factor acts
first, and the equation agrees with the multiplication law of the given
homomorphism into packet permutations. Its inverse proof checks all packet
vertices by applying the inverse ambient permutation to agreement at the
inverse local image. No extension beyond the packet is asserted.

The projection r to E is a group homomorphism, and separate extensions
make it surjective. The proof installs finiteness of E from `IsKleinFour`;
the entire ambient carrier is finite, so the fiber subgroup is finite.

An element in `ker r` has second component equal to one and hence its
ambient component fixes every packet vertex. The map from the kernel to
the actual pointwise stabilizer is an explicitly constructed **group
homomorphism**. It is injective: equality of ambient components, together
with both second components being one, gives equality of the original
kernel elements.

The image packet has cardinal n+1, proved from the injection. Since n≥2,
the existing odd-stabilizer theorem applies. Oddness of the kernel then
follows from divisibility of group cardinalities under the injective
homomorphism. The proof does not substitute a mere cardinal inequality,
which would be insufficient to deduce oddness.

## Literal Sylow section

The odd-kernel quotient lift is applied to the actual surjection r.
Its returned equivalence from a Sylow subgroup to E is accompanied by the
pointwise equation that this equivalence is exactly r's restriction.
Composing its inverse with the Sylow inclusion therefore gives a genuine
homomorphic section of r. Projection to the ambient automorphism component
gives the required homomorphism sigma.

The final packet agreement uses membership of this same section value in
the original fiber subgroup, together with the checked equality
`r (section a) = a`. Thus the ambient map is the actual map constructed
by the quotient lift, rather than an unrelated existential isomorphism.

## Exact scope and faithfulness

The generic lifting statement has no faithfulness assumption on the local
action and correspondingly does not claim that sigma is injective. For
example, a trivial prescribed local action is allowed. The correct general
description is a Klein **action** by ambient automorphisms.

For the obstruction, the separately constructed local Klein action is
faithful. Any kernel element of the lifted homomorphism then acts trivially
on the local packet, so injectivity follows from the packet embedding and
that local faithfulness. This downstream fact must be used when a later
argument needs a nonidentity ambient involution. It is not silently assumed
by the generic lift theorem.

## Verification and frozen sources

An independent build of both targets passed. Standalone signature checks
confirmed their displayed quantifiers and actual automorphism codomains.
Seven selected `#print axioms` checks all report only
`propext`, `Classical.choice` and `Quot.sound`:

- `Preserves.comp`;
- `betweenCopies` and its vertex-value lemma;
- `extend_isomorphism`;
- `packetExtensionGroup`;
- `lift_packet_perm_action`;
- `lift_packet_action`.

Evidence: `../preparation/eppa-lift-independent-build.log` and
`../preparation/eppa-lift-independent-axioms.log`. The authoritative full
receiving-project audit is recorded separately by the integrating package.

| Module | SHA-256 |
| --- | --- |
| `EPPAExtension.lean` | `90c145772f14123cc7f88b7d1b4b5263198ae13582a3cf8619ffda374757ec53` |
| `EPPAKleinLift.lean` | `1433d5dd69e6f4df70d2e1db2e39f23b9b7ae32f5796f91f305c69ed131f159f` |

The author corrected the generic theorem's doc wording from a Klein subgroup
to a Klein action. The final files also directly import their Ext/Omega
tactics. No proof changed; the table pins those final sources.
No proof source was changed by this reviewer.
