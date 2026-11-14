# Independent review of the local packet Klein action

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. Reviewed the actual frozen
`LocalKleinAutomorphisms.lean`, independently of its author. No blocking
mathematical or API issue was found.

The acting group is Mathlib's standard Klein subgroup of the alternating
group on four letters, with its proved `IsKleinFour` instance. The forgetful
homomorphism to the four-point permutation group is injective. Extending it
along the selected four base vertices uses the actual homomorphism
`Equiv.Perm.viaEmbeddingHom`, preserving injectivity and permutation sign.

The four-vertex embedding lands entirely among `Fin n` base coordinates.
Consequently the final packet vertex is fixed, as is every base vertex
outside the chosen image. The proof does not assume the selected vertices
are increasing in an auxiliary order.

Preservation is checked on normalized facets using the exact even-permutation
law. On the selected image the hypothesis identifies every pair of colors;
outside it the permutation is literally identity. The proved facet recovery
then supplies preservation of every injective ordered n-tuple. Thus the
action preserves the full packet, rather than just its base reduct.

The generic construction needs no separate n≥4 premise because its four-point
injection already implies that bound. The local obstruction supplies n≥4
explicitly. Faithfulness is a proved conclusion, and is passed to the later
lifting/saturation argument only after that argument's own lift is shown
faithful on the embedded packet.

The receiving target build passed (1586 jobs) and six selected source exports
were checked by the author to use only the standard three axioms. The full
defining-module audit in the package independently checks every declaration
and all transitive inputs. Reviewed SHA-256:

```
548f0ff58eb166d7137bb73cb6dc7424550136ac394d30aec21aa12efaf54a3c
```

The independent review of the generic ordinary-EPPA fiber lift is recorded
separately in `EPPA_LIFT_REVIEW_2026-11-14.md`; no coherent extension property
or faithfulness premise is silently imported from that generic theorem.
