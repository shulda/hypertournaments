# Independent EPPA foundations review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`; proof preparation
`hypertournaments_formalization_source.tex`, especially the EPPA definitions,
`lem:klein-fixed`, and `lem:coset`.

Reviewed frozen sources:

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/EPPA.lean` | `6ace04aac80ebb6614a8c9c0bd932c5a734775b53c011a87b51fdf3b3acda7bc` |
| `Hypertournaments/KleinFixedPoint.lean` | `6a44a702e9d0794c34cdf648b0e34907ee4fc00ec09e42f194bd67476d80006b` |
| `Hypertournaments/OddCosetFixedPoint.lean` | `8d31b7be880afa576f806e11d2d4b9daa7b29b17082960ed452a880fc0a1f16e` |

No blocking mathematical or interface issue was found. Proof sources were
reviewed without modification.

## Ordinary EPPA and induced partial automorphisms

`Hyper.PartialAutomorphism` uses actual subsets of the original carrier and a
bijection between them. The two orientations in its preservation condition
are literal pullbacks along the subset inclusions. They are not partial
orientation structures with unspecified tuples. Since the vertex map is a
bijection, preservation is exactly an isomorphism of those induced
hypertournaments; inverse preservation follows by applying the same equation
to tuples pulled back along the inverse.

`Hyper.IsEPPAWitness.extension` has the quantifiers
`∀ p, ∃ g, ∀ x` for a genuine whole-carrier `B.Aut`. Thus every partial
automorphism extends separately. There is no choice of a homomorphism from
partial automorphisms, no composition law on the selected extensions, and no
coherent-EPPA requirement. The witness also contains the original
orientation-preserving vertex embedding and an explicit `Finite W` field for
its entire target carrier.

The sets in a partial automorphism need no separate finiteness field: for the
finite source structures used by `HasEPPA`, all their subsets are finite.
The general witness definition itself makes sense on arbitrary carriers; an
embedding into its finite target already forces its source to be finite.
No nonempty-carrier assumption is present.

## Automorphism and finite-carrier transport

`Hyper.Aut.reindex` is the actual conjugate permutation
`s ∘ g ∘ s.symm`. Its target orientation is the pullback along `s.symm`.
The displayed tuple identity therefore proves the original orientation
preservation equation on every injective tuple of the new carrier. There is
no order or sign-normalization change.

`Hyper.IsEPPAWitness.reindex` transports both the original embedding and every
individual extension. It establishes finiteness of the new entire carrier by
the equivalence. In the extension equation the two occurrences of the
equivalence cancel before applying the original equation, so the prescribed
partial automorphism remains the same one on the original source.

`Hyper.IsEPPAWitness.hasFiniteEPPAWitness` is universe-polymorphic and applies
to any actual finite target. It reindexes that target through
`Fintype.equivFin`. Consequently an obstruction stated as
`¬ A.HasFiniteEPPAWitness` excludes witnesses on every finite carrier, not
only a preferred presentation. The converse direction is immediate from the
definition, because a finite-ordinal witness is already an actual finite
witness.

`HasEPPA` uses finite ordinals as representatives for both source and target
structures in an omission class. Its current exported transport theorem
explicitly covers target carriers. A source-reindex equivalence for the class
interface has not been exported here; that routine presentation theorem is
not needed for the local obstruction on a finite-ordinal source. The
unrestricted-obstruction reduction correctly discards the target omission
condition and keeps its actual finite witness.

## Klein fixed-point lemmas

`two_involutions_fixed_witness` needs a finite nontrivial group `Q` and two
involutive automorphisms. If neither has a nonidentity fixed point, the
existing finite fixed-point-free involution theorem identifies each with
inversion. Their product consequently acts as the identity. The argument
does not assume that `Q` is commutative or has odd order, nor that the two
automorphisms commute or generate a faithful action.

`klein_hom_fixed_witness` similarly has no source commutativity or faithfulness
requirement. It requires that `a`, `b`, and `a*b` are nonidentity, and concludes
that one of them fixes a nonidentity element. Its conclusion does not claim
that the chosen source element is involutive.

The stronger `klein_action_fixed_witness` does conclude that the chosen source
element squares to one. It explicitly assumes `Commute a b` and uses that
assumption to prove `(a*b)^2 = 1`. Thus the stronger conclusion has exactly
the additional hypothesis it needs. All three statements require finiteness
and nontriviality of the acted-on group, without requiring the acting group
to be finite.

## Odd invariant cosets

`finite_odd_involution_fixed` applies to a finite odd set; odd cardinality
already excludes the empty case. The restricted permutation is constructed
from the stated involution, and the prime fixed-point theorem is applied with
prime two.

`odd_invariant_coset_fixed_representative` uses the literal left coset
`k J = {x | k⁻¹*x ∈ J}`. Multiplication by `k` identifies its carrier with `J`,
so only `J`, rather than the ambient group, needs to be finite. Forward
stability of `J` and `k⁻¹ * α(k) ∈ J` suffice to restrict `α` to this coset.
The proof uses the ordered product
`(k⁻¹ * α(k)) * α(k⁻¹*x)` and cancellation, without interchanging factors.
It therefore requires neither normality of `J` nor commutativity of the
ambient group. The fixed representative belongs to the required original
coset, with no quotient-group assumption.

## Verification and scope

Focused `#print axioms` checks of the EPPA transport/reduction exports and all
five reviewed group exports reported only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, custom axiom, `native_decide`, or `bv_decide`
occurs in these sources.

These are EPPA definitions, transport and elementary group foundations. They
do not yet establish the local high-arity EPPA obstruction or the main
article's EPPA conclusions; those remain subsequent mathematical work.
