# On homogeneous hypertournaments — supplementary material

[![Lean CI](https://github.com/shulda/hypertournaments/actions/workflows/lean.yml/badge.svg)](https://github.com/shulda/hypertournaments/actions/workflows/lean.yml)

This repository accompanies *On homogeneous hypertournaments* by Matěj
Konečný. It contains the Lean 4 formalization of the mathematical results
and documentation connecting the formalization to the article and its
two supplementary expositions.

## Papers

| Document | Lean reference |
| --- | --- |
| *On homogeneous hypertournaments* | [Main article](https://github.com/shulda/hypertournaments/wiki/Main-article) |
| *Generalised potential structures* | [Potential-structure supplement](https://github.com/shulda/hypertournaments/wiki/Generalised-potential-structures) |
| *Classification of (n+1)-constrained n-hypertournaments* | [Classification supplement](https://github.com/shulda/hypertournaments/wiki/Classification) |

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
