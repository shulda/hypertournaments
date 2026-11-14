# Formalization plan and proof status

Current status, 2026-11-14: the original negative queue, the agreed finite
article, the small-arity cases and the general affine potential construction
are complete. The user subsequently authorized the five-constrained ternary
classification; its source map and exact formulation boundaries are in
[`FIVE_CONSTRAINED_2026-11-14.md`](FIVE_CONSTRAINED_2026-11-14.md).
The continuum/Fraisse corollary remains excluded. The dated plan below is
retained as historical provenance rather than the current work queue.

Date: 2026-11-08.

## Public theorem-level API

`Hypertournaments.HasAP n S` is ordinary AP of the class of finite n-hypertournaments with allowed (n+1)-vertex type indices in S. We intentionally quantify over all vertex embeddings (not just order-preserving ones). The type numbers are the minority counts of normalized facet packets.

Target statement (not yet proved):

```lean
theorem negative_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)\n    (hcentral : centralIndex n ∈ S)
    (hap : HasAP n S) : NecessaryAlternatives n S
```

The well-formedness hypothesis `ValidTypes n S` excludes phantom indices beyond the maximal possible type index; without it, equality with the switching set would be mathematically false. The disjunction says that the next-to-central index is allowed, or n is odd and S is exactly the coboundary/switching parity family. The positive proof will establish AP for both alternatives; the final iff will share the same definitions.

## Scope

- n >= 4 only; n=2 tournaments are **not** part of this task.
- The separate five-constrained ternary classification is stage two.
- Formalize the negative direction without finite hypergraph Ramsey: require the central index explicitly.

## Proof work queue

1. Data model: alternating signs; type completeness/invariance under relabeling; ordinary AP.
2. One-point amalgam obstruction + two-coordinate reflection lemma.
3. Arity 4 and 5 finite seeds (reflection-checkable).
4. Cone, even and rooted odd two-coordinate lifts.
5. Odd 1 mod 4 deterministic family.
6. Odd 3 mod 4 finite counting/disjoint transversals.
7. Induction and final necessary condition.

No source has been formally verified yet. Keep source auditing and Lean proof status distinct. Do not replace the target theorem by an axiom.
