# Independent review: compatible cyclic Ramsey expansions

Reviewed on 2026-11-14 against article source commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, the introduction's compatible
linear-order Ramsey expansion of the homogeneous cyclic order. The
reviewer did not edit the reviewed implementation.

## Frozen source hashes

| File | SHA256 |
| --- | --- |
| `Hypertournaments/CyclicRamsey.lean` | `985383f009212db41ac5a7657b3c802bc6f6037ed9a7c5747851ec8f51766236` |
| `Hypertournaments/CyclicExpansionProperty.lean` | `2fe4ad215ea84789a2ab10a98c32cfbf3babb51dac8f3a7de383cab1d38e653e` |

## Ramsey statement and actual embedding transport

`compatibleCyclicExpansionClass` requires finiteness of the entire
carrier and an actual intrinsic ternary hypertournament together with
a linear order inducing its strict circular relation. The native
structure names both the orientation relation and this order. Thus
membership imposes the stated compatibility condition; the result is
not about arbitrary orders on a fixed cyclic-order reduct.

The pure auxiliary language has no relation or function symbols. Its
models on a carrier are proved unique. The Ramsey input is the existing
pinned theorem `CCO.UnaryHN.Native.allOrderedModels_ramsey`, whose
conclusion is an actual finite ordered target satisfying the native
`Structure.Arrow`. The proof extracts its full carrier and actual
linear order, identifies its empty-language reduct with the unique
pure model, and circularizes that order to construct the intrinsic
witness `D`. The required circular compatibility of `D` is proved.
No completion predicate or uninstantiated Ramsey provider replaces the
actual target.

The forget map retains the same underlying injection and the full
order-relation equivalence. The lift map obtains a strictly increasing
injection from a pure ordered embedding. The source and target
compatibility certificates then prove intrinsic orientation
preservation. `orderedEmbedding` converts this into a full native
embedding: its orientation relation is preserved and reflected on all
ternary tuples, including repeated coordinates, using
`preserves_iff_relation`; its named strict order is also preserved and
reflected. The empty function-symbol case is discharged explicitly.

The coloring is pulled back along this actual lift. For every native
embedding of the source into the middle structure, forgetting its
orientation and composing with the pure Ramsey embedding gives the
same vertex function as composing it with the lifted native Ramsey
embedding. The proof establishes equality of these embeddings by
pointwise extensionality. Consequently monochromaticity is exactly
native `Structure.Arrow`, with the original full embeddings. The final
`cyclic_expansions_ramsey` theorem packages the constructed witness in
the stated native class and the existing native `Ramsey` interface.

## Expansion property and boundaries

`cyclic_compatible_expansions_embed` uses the increasing enumerations
of a finite carrier to obtain an actual order isomorphism between the
two supplied linear orders. Because both orders induce the same
intrinsic cyclic order, the increasing bijection preserves that
orientation as well. Its conclusion is an actual native embedding of
the two expanded structures.

In `cyclic_expansion_property`, the witness is literally `B = A` on the
same finite carrier. It is chosen before either compatible order is
quantified. The conclusion therefore has the correct expansion-property
quantifier order: every compatible expansion of `A` embeds into every
compatible expansion of this one fixed witness. The argument includes
the empty carrier and does not choose a distinguished vertex or assume
inhabited source/target carriers.

The Ramsey theorem quantifies over arbitrary finite source and middle
carriers in `Type v`, and every finite nonempty color type in an
independent `Type w`. Its finite target remains in `Type v`. Both the
witness theorem and the class theorem explicitly retain the standard
`Fintype` and `Nonempty` color assumptions. There is no nonempty-carrier
assumption and no hidden color bound.

## Independent verification

- `lake build Hypertournaments.CyclicRamsey Hypertournaments.CyclicExpansionProperty`
  passed, 1252 jobs. The reviewed modules emitted no warnings; the build
  replayed existing dependency warnings.
- A defining-module audit enumerated all 26 declarations attributed to
  the two modules, including private helpers and generated declarations.
  Transitive axiom collection admitted only `propext`,
  `Classical.choice`, and `Quot.sound`; all declarations passed.
- A separate kernel-checked empty-carrier example instantiated the
  compatible-expansion embedding theorem on an arbitrary intrinsic
  structure on `Fin 0` and any two linear orders, proving compatibility
  vacuously.
- A separate kernel-checked Ramsey specialization used carriers
  `ULift.{1} (Fin 0)` and `ULift.{1} (Fin 1)`, target universe `Type 1`,
  and colors `ULift.{1} (Fin 2)`. This checked the empty-source boundary
  and nonzero carrier/color universes through the actual public
  `Structure.Arrow` conclusion.

No mathematical or interface defect was found. The two modules prove
actual finite Ramsey witnesses and the expansion property for the
compatible-order expansion class claimed in the source.
