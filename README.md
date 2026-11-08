# Formalization of constrained hypertournaments

Lean 4 / Mathlib formalization supporting the negative and positive amalgamation classifications of finite hypertournaments.

**Current focus:** the negative necessary condition for amalgamation in the \((n+1)\)-constrained, \(n\)-ary case, for \(n\ge4\). Arity two and the separate five-constrained ternary classification are deliberately out of scope for this stage.

The source mathematical argument is an AI-written working note, **not yet Lean-verified**. The repository is organized to distinguish kernel-checked statements from pending proof obligations. In particular, no theorem is marked verified until CI builds it without `sorry`, `admit` or additional axioms.

## Intended theorem-level interface

Let \(q=\lfloor(n+1)/2\rfloor\), and let \(S\) be an allowed set of isomorphism types of \((n+1)\)-vertex \(n\)-hypertournaments. If the central type \(q\) is allowed and the associated finite class has AP, then either:

- the next-to-central type \(q-1\) is allowed; or
- \(n\) is odd and \(S\) is precisely the parity/coboundary (switching) family \(E_n\).

The positive classification will later establish AP for the first alternative and the switching family, producing an iff theorem. The Lean statements and their mathematical interpretation are subject to detailed source audit.

See `notes/` and `Hypertournaments/` on the development branch.
