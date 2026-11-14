# Independent EPPA transfer review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer` and `cor:even-no-eppa`, compared with the expanded
proof preparation. Reviewed frozen `OnePointLink.lean`,
`EPPASourceTransport.lean`, `EPPATransfer.lean`, and `EvenNoEPPA.lean`.
No blocking mathematical or API issue was found. The reviewer did not change
the four reviewed proof files.

## Intrinsic links and source transport

`onePointTuple` prepends the actual distinguished vertex to an injective
lower-arity tuple. The lifted permutation fixes its first coordinate and
has exactly the original permutation's sign. Consequently `onePointSlice`
and the full `onePointLink` satisfy the actual alternating orientation law.
No vertex order, finiteness, or evenness assumption is imposed on the upper
structure when defining its link.

An ambient automorphism fixing the distinguished vertex preserves its
complement in both directions. `Hyper.Aut.onePointLink` restricts that
actual permutation and proves its orientation preservation by equality
of the prepended tuples. It does not assume an induced map on the link
without proving preservation.

The source-transport lemmas use the original ordinary EPPA witness and
its proved `extend_isomorphism` interface. For an induced lower source,
the two copies are the original partial domain and its image, mapped
through the supplied source embedding. Thus the returned automorphism
has the required equation along the original composite embedding.
`HasEPPA.exists_witness` transports an arbitrary finite source through
an equivalence with `Fin`; it retains actual target-family membership
and returns a witness for the original source. There is no coherent
extension choice or extra amalgamation premise.

## Cone witness and arity lowering

`evenCone_witness_link` uses the even cone on `Option V`, with root `none`.
Its embedding into the upper witness yields an actual lower embedding
into the complement of the root's image. The root-orientation equation
proves preservation of the original lower structure.

For each lower partial automorphism, the proof takes the cone over its
actual source subtype. The inclusion and partial isomorphism give two
orientation-preserving lower embeddings, and full cone naturality lifts
both to embeddings which fix the root. Ordinary upper EPPA therefore
extends the induced isomorphism between these copies. Its displayed
extension equation at `none` proves that the resulting ambient
automorphism fixes the root. Only then is it restricted to the full link.
The equation at `some x` is exactly the required lower extension equation.

This also handles an empty lower partial domain: its cone still contains
the root, so the argument establishing root fixation remains present.
There is no choice of extensions required to respect multiplication.
The upper witness is not assumed even; the proof only uses its finite
carrier, preservation of the cone, and ordinary extension property.

The two class wrappers apply the original `HasEPPA` interface. For the
even upper class, the cone's proved `IsEven` property and the established
switching-family equivalence supply its source-family membership. The
link is an unrestricted lower witness, so no closure claim about even
links is needed. Reindexing its finite target returns the original
finite-ordinal class interface.

`eppa_one_arity_down` has the literal source range: every odd upper arity
`n >= 3`, from either unrestricted upper EPPA or even upper EPPA to
unrestricted EPPA in arity `n - 1`. It has no additional congruence
restriction, provider hypothesis, or unresolved source instance.

## Non-EPPA consequence

`even_not_hasEPPA` applies the transfer and the already proved
`pair_cancelling_not_EPPA` to the empty forbidden family in arity
`n - 1 >= 4`. Empty-family pair cancellation is discharged by its actual
proved instance. This gives failure of ordinary EPPA for the even class
in every odd arity at least five, including the exported concrete
`even_five_not_hasEPPA`. The local obstruction and its group-theoretic
dependencies are covered by the separate obstruction review.

## Validation and frozen snapshots

An independent four-target build passed (1753 jobs). Focused axiom prints
for the restricted-link automorphism, source pullback, arbitrary-source
witness extraction, cone-witness link, literal arity-lowering theorem,
general even non-EPPA theorem, and arity-five instance all reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. Additional Lean examples
checked that the link of a ternary structure is a binary structure and
that each upper-class hypothesis specializes to the transfer from arity
three to arity two. A scan of all four reviewed files found no `sorry`,
`admit`, custom axiom, `native_decide`, or unsafe declaration.

Evidence: `../preparation/eppa-transfer-independent-build.log`,
`../preparation/eppa-transfer-independent-check.lean`, and
`../preparation/eppa-transfer-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `OnePointLink.lean` | `e8537ccee93e8be05606f8e36f42e2c2e1d0ae29e97481e7da4f8eb37b6bd13c` |
| `EPPASourceTransport.lean` | `1feaa0d6f3bba3cc2d6f7f31437943b695e819c718b260b160dc59373c9e922e` |
| `EPPATransfer.lean` | `56b30a2c3fcfeffaf2a9d31ee85d4efd87dba7b44669aead2b0861c7ab8ff766` |
| `EvenNoEPPA.lean` | `b0c7450b49fceac68bb7f92008d131cfd5772d393270276d103b6ec95d6cff95` |
