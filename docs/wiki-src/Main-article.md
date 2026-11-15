# On homogeneous hypertournaments

This chapter matches the main results of Matěj Konečný's *On homogeneous
hypertournaments* with their Lean statements. The numbering is that of the
source revision recorded in the [statement catalogue]({{repo}}/blob/main/docs/catalogue/papers.json).
The TeX labels and full Lean declaration names are the stable identifiers.

The introductory theorems summarize results proved later in the paper, so
some declarations appear under both their introductory and later labels.
The companion chapters explain [generalised potential structures](Generalised-potential-structures)
and the [classification results](Classification) in more detail.

## Reading the formal statements

A hypertournament is an alternating Boolean orientation on injective ordered
tuples. Vertex embeddings preserve the entire orientation and need not preserve
any auxiliary order. See [Mathematical definitions](Mathematical-definitions)
for this common language.

The local packet index is a minority count of normalized facet signs; it is
invariant under every vertex permutation. Allowed-index classes use this
intrinsic index. Their ordinary AP allows extra identifications, whereas the
strong AP statements require exactly the prescribed overlap.

The pair-cancelling omission result permits an arbitrary family of finite
obstructions. Its Ramsey expansion consists of **all** linear orders on the
admitted finite structures. In the potential construction an expansion names
both an actual lower-arity potential and an arbitrary linear order. The
expansion-property target is fixed before the later potentials and orders
are chosen.

The EPPA obstruction results concern arbitrary finite witnesses and arbitrary
orientation-preserving embeddings. Their conclusions exclude ordinary EPPA;
they are not restricted to one attempted witness construction.

The continuum corollary constructs countably infinite homogeneous structures
and identifies their actual finite ages. The strict constraint hierarchy uses
one obstruction at every size `k > n`, including the smallest sizes; it does
not rely on a large-size antichain bound.

## Article-to-Lean correspondence

Each block records the precise parameter range and the defining Lean files.
“Background instance” means the library supplies the instance used here of
a theorem cited in the preliminaries. “Definition” identifies the common
objects rather than asserting an additional theorem.

{{table:main}}
