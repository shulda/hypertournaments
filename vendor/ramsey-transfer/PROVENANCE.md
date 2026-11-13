# Pinned Ramsey transfer closure

This directory contains the exact transitive Lean import closure of
`CCO.UnaryHN.IteratedTransfer` and `CCO.UnaryHN.OrderedAmbient` from
`shulda/lean_cco` at commit `48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6`.
The 119 source modules comprise 14 CCO modules, 87 PartiteConstruction
modules, and 18 SuccessorTree modules. Every source byte is unchanged.
`SOURCE_MANIFEST.json` records source paths, exact Git blob identities,
SHA-256 hashes, imports, and a deterministic aggregate source digest.

The CCO pin already contains the Lean 4.34.1 receiving compatibility port
of the Ramsey sources. The original upstream source map and compatibility
patch are retained in `provenance/`. Their hashes refer to the original
upstreams; the manifest in this directory identifies the exact received files.

The local CCO library retains the receiving package's explicit-variable options.
PartiteConstruction and SuccessorTree retain their original separate package's
default implicit-variable options. No Mathlib pin is changed.

There is no dependency on the CCO facade, its EPPA package, or its
factorization-forest package. Mathlib and Lean imports remain external.
`tools/project_sources.py` validates this snapshot and traverses its imports
when deriving Mathlib cache roots for the receiving project.

The SuccessorTree CC0 notice is preserved as `LICENSE.SuccessorTree`.
See `LICENSES.md` for the scope of retained licensing information.
