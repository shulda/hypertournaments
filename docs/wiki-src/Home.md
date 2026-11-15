# Hypertournaments — the Lean library

This library formalizes the main amalgamation, Ramsey-expansion, EPPA and
classification results associated with Matěj Konečný's *On homogeneous
hypertournaments*. It also supplies the finite structures and countable
homogeneous limits used by the continuum corollary.

The documentation follows three companion texts:

| Text | Lean reference |
| --- | --- |
| *On homogeneous hypertournaments* | [Main article](Main-article) |
| *Generalised potential structures* | [Generalised potential structures](Generalised-potential-structures) |
| *Classification of (n+1)-constrained n-hypertournaments* | [Classification](Classification) |

Each reference chapter connects the text's stable labels and displayed
statement numbers to complete Lean names, defining files and source lines.
The statements' arity, finiteness and embedding assumptions are recorded
alongside the links. Research discussions and conjectures are outside this
theorem index.

## Find your starting point

| You want to… | Start here |
| --- | --- |
| Build the project or use it as a dependency | [Using the library](Using-the-library) |
| Understand orientations, embeddings, local types and potentials | [Mathematical definitions](Mathematical-definitions) |
| Find a theorem from the main article | [Main article](Main-article) |
| Use the finite-palette, abelian-group potential construction | [Generalised potential structures](Generalised-potential-structures) |
| Find the local amalgamation classifications or finite obstruction proofs | [Classification](Classification) |
| Start from a Lean file and find its paper statements | [Lean file index](Lean-file-index) |
| Follow the constructions behind the results | [Proof architecture](Proof-architecture) |
| Reproduce the kernel and source checks | [Verification](Verification) |
| Maintain the pages or prepare links from a paper | [Publishing](Publishing) |

## Main entry points

```lean
import Hypertournaments

#check Hypertournaments.pair_cancelling_hasStrongAmalgamation
#check Hypertournaments.Ramsey.pair_cancelling_ordered_ramsey
#check Hypertournaments.Ramsey.pair_cancelling_ordering_property
#check Hypertournaments.Hyper.isEven_iff_exists_potential
#check Hypertournaments.amalgamation_classification
#check Hypertournaments.strict_constrained_hierarchy
#check Hypertournaments.continuum_homogeneous_hypertournaments
```

The canonical documentation sources and the machine-readable statement map
are maintained with the Lean code. The [publishing guide](Publishing)
explains how these pages and their source links are generated.
