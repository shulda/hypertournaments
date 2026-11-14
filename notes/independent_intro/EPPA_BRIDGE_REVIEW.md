# Independent review of the EPPA bridge

Date: 2026-11-14. Reviewer: the `independent_bridge_basic` agent, which did
not author `EPPABridge.lean`. Verdict: **PASS**. No changes to the reviewed
Lean source were needed.

## Frozen sources

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/Independent/EPPABridge.lean` | `1c9916c615fd6963fd295c4cfbe2c448c0806c64ba903090bca41b4cec70bf18` |
| `Hypertournaments/Independent/BasicBridge.lean` | `44a9ff88442bdfe4f4d97ecf022793306fda8b0758ce0496b24a9c55c957aca8` |
| `Hypertournaments/Independent/ClassBridge.lean` | `956df22323364fdf61d32e61bc8e297d48e9a0c60698c2f26ac64d6265cb6fa7` |

The EPPA source hash was checked both before and after the review.

## Mathematical checks

1. **Arbitrary independent classes.** `nativeClass` evaluates the original
   predicate at `ofHyper A` on the same `Fin m`. All reconstruction steps use
   the proved equality `ofHyper (toHyper A) = A`, not merely an isomorphism.
   Consequently neither EPPA transfer nor heredity, unboundedness or SAP
   assumes that the independent predicate is already isomorphism invariant.

2. **All partial automorphisms, one fixed witness.**
   `partialTotal_isPartialAutomorphism` covers every native subset
   isomorphism. It uses the actual bijection on its domain and the identity
   elsewhere, so empty domains and carriers require no chosen vertex.
   Injective tuples use precisely `p.preserves`; degenerate tuples use the
   independent standardized zero value. In `hasEPPA_to_nativeClass`, the
   independent witness `B` and its inclusion are extracted before the
   arbitrary native partial automorphism is introduced (lines 89-98).
   The extending map is converted from a genuinely bijective automorphism
   to a permutation; no injective-endomorphism substitution occurs.

3. **Exact strong amalgamation.** The original maps into both sides are
   retained. The independent strong amalgam supplies the same commuting
   equations and exact-intersection implication used by the native class
   interface. Lines 133-143 transport its membership and orientation laws
   while passing `hcomm` and `hinter` unchanged. No extra identifications or
   stronger class hypotheses are introduced.

4. **The three conclusions.** Part (i) invokes the existing theorem for
   unbounded hereditary SAP classes with exactly the transferred hypotheses.
   Part (ii) uses the exact `omits_iff` bridge in both directions and the
   translated pair-cancelling family hypothesis; arbitrary, infinite and
   empty forbidden families remain allowed. Part (iii) translates between
   the intrinsic evenness equation and the existing switching omission
   class in both directions, for arbitrary finite carriers in arity five.
   Thus the source class and the returned witness class are the required
   classes, including small and empty structures.

5. **Final target.** `IndependentHypertournaments.intro_eppa` proves the
   original independent `IntroEPPAStatement` by all three parts. The adapter
   establishes the direction independent EPPA implies native EPPA, which is
   sufficient for the negative conclusions; it does not rely on an
   unproved reverse implication or replace any target definition.

## Kernel check

An additional direct check of the frozen source succeeded with exit code
zero and no diagnostics:

```sh
lake env lean Hypertournaments/Independent/EPPABridge.lean
```

Lean version: 4.34.1, using the repository's pinned dependency manifest.
The complete project axiom audit and proposed-head CI remain separate
integration checks performed by the parent task.
