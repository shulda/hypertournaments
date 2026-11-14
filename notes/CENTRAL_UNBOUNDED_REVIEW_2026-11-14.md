# Independent central-type/unboundedness review, 2026-11-14

Reviewed the frozen `Hypertournaments/CentralUnbounded.lean`, SHA-256
`83434a8478767118e15b33b602d257763285b43f60a24df4fb41a4082a815df6`.
The proof source was not edited. The relevant unboundedness discussion in
the recovered formalization preparation for `shulda/tex_hypertournaments`
at `919349e7eceed3c7fa0ed126a337c6fae6624704` was also checked.

No mathematical or API issue was found. The module proves the full
equivalence between central-type membership and arbitrarily large finite
admissible structures, with no AP, heredity, validity, parity, or positive
arity premise.

## Exact quantifiers and the sufficient direction

`UnboundedAdmissible n S` means that for every natural-number bound `N`
there is a cardinality `m >= N` and an actual intrinsic `Hyper n (Fin m)`
which is `Admissible S`. This is a statement about arbitrarily large
finite structures, not the existence of one infinite structure.

The sufficient direction supplies cardinality exactly `N`, using
`Hyper.fromOrderedSigns` with the constant false canonical sign. On each
increasing `(n+1)`-tuple its raw facets have that constant sign.
`admissible_iff_canonical_all` then extends the check to every injective
tuple using the already proved all-permutation local-index invariance.
The auxiliary order used to define canonical signs is not added to the
intrinsic hypertournament or admissibility relation.

## All-arity constant-packet count

The private counting lemma treats either common raw Boolean value. With
`k` facets, normalization gives `xor b (decide (i % 2 = 1))`, whose number
of positive entries is `k / 2` for `b = false` and `k - k / 2` for
`b = true`. The induction explicitly complements the initial raw bit
when passing to the successor tail. Thus
`localIndex_eq_central_of_constant_facets` takes the minimum of the two
complementary counts and obtains `centralIndex n` for all `n`.

No division/subtraction step uses an unstated lower bound on `n`. The
proof includes `n = 0`, whose packet has one facet and central index zero,
and `n = 1`, whose two normalized facets have minority count one. Separate
Lean examples specializing the final equivalence to those arities passed:
`UnboundedAdmissible 0 S <-> 0 in S` and
`UnboundedAdmissible 1 S <-> 1 in S`.

## Native finite Ramsey bridge and actual orientations

The Ramsey input is `CCO.UnaryHN.Native.allOrderedModels_ramsey` applied
to an empty relation/function language, expanded by its genuine strict
linear-order symbol. The models of sizes `n` and `n+1` use their ordinary
finite orders. Their membership proofs establish the required native
`AllOrderedModels` predicate; singleton-valued functions are vacuous
because the function-symbol type is empty. The Ramsey palette is the
finite nonempty type `Bool`. No Ramsey property of the admissible class
is assumed, directly or conditionally.

The returned Ramsey witness has a finite whole carrier `V`. Unboundedness
is invoked at `Fintype.card V`, giving `m` at least that cardinality and
an admissible hypertournament on `Fin m`. The injection `e : V -> Fin m`
is the composition of the actual `Fintype.equivFin` embedding and the
cardinality-bound embedding `Fin.castLEOrderEmb`. There is no unsupported
assumption identifying `V` with an ambient subset or requiring `e` to
preserve the order of the Ramsey witness.

The coloring assigns to each native embedding of the `n`-point order the
raw orientation of its actual injective ordered tuple after composition
with `e`. Each `orderedPureFacet i` is a genuine native embedding supplied
by `Fin.succAboveOrderEmb i`: it preserves and reflects the fresh order
relation, and all old symbols are vacuous. The native arrow returns an
embedding `g` of the `(n+1)`-point order. Composing its underlying injection
with `e` gives the literal ambient tuple `f` used in the conclusion.

Native embedding composition and `facet` both compose those same vertex
maps. Consequently the arrow's equality of the colors of
`g.comp (orderedPureFacet i)` and `g.comp (orderedPureFacet 0)` is exactly
the displayed equality of the corresponding raw facet orientations of
`f`. This equality is accepted directly by Lean, without a replacement
coloring, an image-only surrogate, or a preservation hypothesis. The
constant-packet theorem supplies the central index, and `hA f` supplies
its actual membership in `S`. The construction is valid for the empty
source order at `n = 0` as well.

## Verification

`lake build Hypertournaments.CentralUnbounded` passed with 1623 jobs;
replayed dependency warnings do not concern this new module. Explicit
`#print axioms` checks passed for all four public theorem exports:

- `localIndex_eq_central_of_constant_facets`;
- `unboundedAdmissible_of_central`;
- `central_of_unboundedAdmissible`;
- `unboundedAdmissible_iff_central`.

Each depends on exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no remaining conditional mathematical inputs in this module.
