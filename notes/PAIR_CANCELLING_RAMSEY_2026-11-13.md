# Arbitrary-relational completion and the pair-cancelling Ramsey theorem

## Sources and public result

The mathematical source is `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, principally
`prop:link-completion` and `thm:Ramsey`. The proof preparation's direct
last-missing-pair completion was integrated in PR 410; this package supplies
its arbitrary-relational interface and discharges the Ramsey transfer inputs.

`Hypertournaments/PairRamsey.lean` exports:

- `Ramsey.pair_cancelling_ordered_ramsey`: for every n >= 3 and every possibly
  infinite family of finite pair-cancelling structures, the free ordered
  omission class is Ramsey.
- `Ramsey.exists_ordered_ramsey_witness`: for arbitrary finite ordered source
  `Hyper` structures omitting the family and every finite nonempty colour
  palette, there is an actual finite `Hyper` witness, a linear order, actual
  omission, and the full structural Ramsey arrow.

The native class is defined on the whole carrier as finiteness plus an exact
presentation by an ordered `Hyper` that omits the given family. All class,
completion and local-finiteness obligations are proved. No Ramsey, completion,
SAP, or small-pattern provider remains as a premise of the public theorem.

## Relational interfaces

`RamseyLanguage` uses one n-ary relation and no functions; its ordered language
adds the distinguished binary comparison relation. Orientation `false` is
relation truth, and repeated-coordinate tuples are excluded. The existing
`Hyper` and `Preserves` remain the orientation and embedding foundations.
Native full embeddings match the original orientation-preserving embeddings
and strict order embeddings.

An arbitrary candidate is a `StructuralRamsey.Structure` in this same
language, with arbitrary R and comparison relations. It is not assumed to be
a total or already consistent partial hypertournament. Its positive relation
tuples have irreducible supports even with repetitions. The irreducible-piece
hypothesis then supplies a genuine ordered hypertournament on each support,
forcing injectivity and comparison-clique support. Conversely, comparison
cliques are irreducible and supply complete consistent orientations.

`Ramsey.partialOrientation` prescribes exactly those comparison cliques,
reading their orientation from the original R relation. The alternating law
is derived from actual induced models. The missing pairs are exactly distinct
uncompared vertices, and the domain is expressed through tuple ranges.
A fully prescribed forbidden copy has comparison-clique image, using its PC
pair-link witnesses. The original omission of that induced model excludes it.

`Ramsey.exists_relational_completion` has the article's two hypotheses:
its comparisons admit a linear extension, and every irreducible piece belongs
to the freely ordered omission class. It returns an actual forbidden-free
ordered `Hyper` on the same carrier. The identity globally preserves all old
positive relations and is a full embedding on every old irreducible source.
It may add relation tuples and comparisons outside these sources.

## Exact irreducibility and homomorphism-embedding semantics

The article defines relational irreducibility by coverage of every distinct
pair by a positive relation tuple. The native library uses universal
no-crossing irreducibility. `Ramsey.irreducible_iff_pair_coverage` proves their
equivalence in every empty-function language, without a finiteness premise.
The nontrivial direction decomposes a structure missing a pair into the two
induced complements of its endpoints.

The paper-facing `RelationalIrreduciblesIn` predicate is proved equivalent
to native `IrreduciblesIn`. Thus the completion hypothesis is unchanged, not
strengthened to a separate unverified native condition.

Native HN uses `IsEHNHomomorphismEmbedding`, whose global function law is weaker
than the similarly named full interface in `Structure.FreeAmalgam`.
`Ramsey.fullHE_iff_nativeHE` proves exact agreement here: the function alphabet
is empty. Both interfaces preserve relations globally and reflect on old
irreducibles. The completion map is literally `id`, hence injective globally.

## HN application and dependency closure

`RamseyClass` proves whole-carrier finiteness, heredity, singleton-valuedness,
strong amalgamation, ambient inclusion and irreducibility. The SAP construction
uses the actual compatible ordered spans already formalized in this project,
including empty bases. It does not assume membership of the base separately.

In the local-finiteness test, the projection into the ambient ordered control
may be noninjective. Its positive preservation of comparisons gives a linear
extension by `Structure.exists_linearOrder_extension`. Arbitrary-relational
completion then applies directly; the small-completion test is unnecessary.
The genuine HN predicate is proved with cutoff one, in the required quantifier
order. The ambient theorem is `allOrderedModels_ramsey`; the subclass transfer
is `original_unary_locally_finite_ramsey`.

Their exact transitive source closure is copied unchanged from
`shulda/lean_cco` at `48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6`:
14 CCO, 87 PartiteConstruction and 18 SuccessorTree modules. Provenance,
source/blob hashes, original compatibility records and licensing notices are
in `vendor/ramsey-transfer`. No whole-CCO, EPPA or factorization-forest package
is needed. The provider implicit-variable compiler options are retained;
Lean 4.34.1 and the receiving Mathlib/manifest pins are unchanged.

`tools/project_sources.py` verifies the immutable source snapshot and traverses
its imports when determining Mathlib cache roots. Every one of the 119
vendored modules is in the project's audited import closure.

## Validation and review

The machine-readable build, source-digest and full axiom-audit receipt is
`notes/verification/pair_cancelling_ramsey_2026-11-13.json`.
CI builds the exact proposed head and audits all declarations defined in the
Hypertournaments, CCO, PartiteConstruction and SuccessorTree module prefixes.
The allowlist is exactly `propext,Classical.choice,Quot.sound`.
Selected axiom prints supplement, rather than replace, these complete audits.

Focused mathematical reviews covered the extraction from arbitrary inputs,
pair-coverage equivalence, noninjective projection, exact HE semantics,
whole-carrier membership, all HN hypotheses, empty cases and colour/witness
quantifiers. The separate vendor replay also checks the original exported
Ramsey theorem signatures and their standard axioms.

## Remaining article work

The ordering property, potential/even expansions and their expansion property,
finite-group non-EPPA arguments, local-type PC cutoff and the positive
constrained classification remain subsequent tasks. This package proves the
finite Ramsey theorem, not the infinite antichain or Fraisse-limit existence
side results. Five-constrained ternary classification remains postponed.
