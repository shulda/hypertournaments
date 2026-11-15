# On homogeneous hypertournaments — supplementary material

[![Lean CI](https://github.com/shulda/hypertournaments/actions/workflows/lean.yml/badge.svg)](https://github.com/shulda/hypertournaments/actions/workflows/lean.yml)

This repository accompanies *On homogeneous hypertournaments* by Matěj
Konečný. It contains the article, two supplementary expositions, and the
Lean 4 formalization of the mathematical results.

The manuscripts refer to the [Lean source snapshot `97ece7669d91`](https://github.com/shulda/hypertournaments/tree/97ece7669d91ffeff83227cc2d2b8cd64f141bfd).

## Papers

| Document | PDF |
| --- | --- |
| *On homogeneous hypertournaments* | [Main article](papers/on_homogeneous_hypertournaments.pdf) |
| *Generalised potential structures* | [Potential-structure supplement](papers/generalised_potential_structures_proof.pdf) |
| *Classification of (n+1)-constrained n-hypertournaments* | [Classification supplement](papers/hypertournaments_classification_supplement.pdf) |

## Documentation and Lean

- The [researcher Wiki](https://github.com/shulda/hypertournaments/wiki)
  explains the definitions, statements, proof architecture and verification.
- The [paper-to-Lean reference](https://github.com/shulda/hypertournaments/wiki/Main-article)
  connects article statements to Lean declarations. The Wiki has separate
  chapters for both supplements and a [Lean file index](https://github.com/shulda/hypertournaments/wiki/Lean-file-index).
- The [Lean sources](Hypertournaments) are re-exported by
  [Hypertournaments.lean](Hypertournaments.lean):

```lean
import Hypertournaments
```

The [machine-readable correspondence](docs/theorem-map.json) records stable
paper labels, full Lean names and checked source locations. Readable copies
of the Wiki pages are also available [in the repository](docs/wiki/Home.md).

The [getting-started guide](https://github.com/shulda/hypertournaments/wiki/Using-the-library)
contains build and dependency instructions. Lean and Mathlib are fixed by
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json).

The Ramsey infrastructure uses Jan Hubička's
[PartiteConstruction](https://github.com/janhubicka/partite-construction) and
[SuccessorTree](https://github.com/janhubicka/lean-successors) libraries.
Their required sources, notices and supplied license text are retained with
the vendored code.
