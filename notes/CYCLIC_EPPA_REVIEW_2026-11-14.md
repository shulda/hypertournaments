# Independent review: finite cyclic-order EPPA obstruction

Reviewed on 2026-11-14 against article source commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, the unnumbered finite
cyclic-order argument following `cor:even-no-eppa`. The reviewer did not
edit either reviewed implementation.

## Frozen source hashes

| File | SHA256 |
| --- | --- |
| `Hypertournaments/CyclicEPPA.lean` | `c72f29cc9c2eb56326009675571a504ec111e8d700008c1eec2d1ca267c93338` |
| `Hypertournaments/CyclicLocalEPPA.lean` | `81ce37957caac28b7922c7a00373e0f2ea04f304906f22d736a1a30eec3a5424` |

## Mathematical and interface checks

The implementation proves the article's finite cyclic-class obstruction.
Its proof is a valid simplification: use the partial isomorphism
`{a,b} -> {a,c}` fixing `a` and sending `b` to `c`, instead of comparing
two separate extended transpositions. Two-point ternary structures have
no injective oriented triples, so this map really preserves every
orientation. `preserves_ternary_from_two` proves this by the impossible
injection `Fin 3 -> Fin 2`; it assumes no source orientation convention.

`Hyper.IsEPPAWitness.extend_isomorphism` constructs a partial
automorphism between the literal ranges of its two injections. Thus the
extension used here is supplied by ordinary, separate EPPA. The proof
does not assume coherent extensions, a prescribed group action, or a
stronger notion of EPPA. The two ranges may overlap at the fixed vertex.
The extended automorphism acts on the actual entire target carrier.

Finite rigidity is proved rather than assumed. Given a circular-order
presentation of the target, an orientation-preserving automorphism
preserves its strict circular relation on pairwise distinct triples.
If it fixes `p`, `CircularOrder.cutLinearOrder_strictMono` makes it
strictly increasing on the full linear order cut at `p`. Mathlib's
`StrictMono.apply_eq` for finite linear orders then fixes every vertex.
This does not require a separate unformalized theorem identifying the
automorphism group with a rotation group, or any classification of
finite permutation groups.

The obstruction theorem obtains `Finite W` from the actual
`IsEPPAWitness.finite` field. It has no hidden supplied finite-target
class instance, no bound on the witness size, and no assumption that
source and target coincide. The embedding `s : Fin 3 -> V` supplies three
distinct source vertices. The extension fixes `e(s 0)` and sends
`e(s 1)` to `e(s 2)`. Rigidity makes it the identity; the contradiction
uses injectivity of both original embeddings `e` and `s`.

The target circular-order hypothesis remains explicit in
`Hyper.not_isEPPAWitness_cyclic_of_three`. The resulting class theorem
quantifies only over witnesses belonging to `cyclicOrderClass`. There
is no assertion that a ternary structure has no unrestricted finite
EPPA witness. This boundary is essential because unrestricted ternary
EPPA is outside the proved result.

The class-level witness is the concrete three-element model
`cyclicThree`, with its actual circular-order certificate. The local
wrapper identifies the whole class with omission of
`localForbiddenFamily 3 {2}` by extensional equality at every finite
carrier size. The equivalence `Admissible {2} A <-> A.IsCyclicOrder` has
no minimum-cardinality premise. In particular the wrapper retains
carriers with fewer than four vertices, rather than silently discarding
the three-vertex obstruction. The transition from `ClassHasEPPA` to
`HasEPPA` uses the existing literal omission-class interface.

## Independent verification

- `lake build Hypertournaments.CyclicEPPA Hypertournaments.CyclicLocalEPPA`
  passed, 1532 jobs. Neither reviewed module emitted a warning. Existing
  warnings replayed from `FinitePresentation` and `TwoPadIntrinsic`.
- Independent `#print axioms` checks covered all eleven declarations in
  the two defining modules. Every result used only
  `propext`, `Classical.choice`, and `Quot.sound`.
- A separate kernel-checked specialization used an arbitrary target
  type `W` with no supplied `[Finite W]` and recovered the obstruction
  directly from a proposed witness into a cyclic target.
- Separate kernel-checked examples recovered circular-order witnesses
  for arbitrary ternary structures on `Fin 0`, `Fin 2`, and `Fin 3` via
  vacuous `{2}` admissibility. These check the small-carrier boundary
  used in the class equality and the obstruction source.

No mathematical or interface defect was found. The results prove
ordinary EPPA failure inside the finite cyclic-order class, including
its exact central-only local-index presentation.
