# Füredi's stability theorem and the Erdős–Simonovits stability theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Turán's theorem (in Mathlib) says that a graph on `n` vertices without a clique `K_{p+1}` has at
most `t(n, p)` edges, the number of edges of the Turán graph. This repository formalizes the
**stability** theory of Turán's theorem. None of these results is in Mathlib. All statements are
in the namespace `TuranStability`.

**Füredi's theorem (2015) for cliques**

* `card_edgeSet_add_le`, Füredi's partition inequality. Every `K_{p+1}`-free graph has a
  partition `V₁, …, V_p` with `e(G) + Σᵢ e(G[Vᵢ]) ≤ e(K(V₁, …, V_p))`.
* `furedi`. A `K_{p+1}`-free graph with at least `t(n, p) − t` edges has a `p`-partite subgraph
  with at least `e(G) − t` edges.
* `exists_partition_symmDiff_le`. Such a graph is at edit distance at most `3t` from a complete
  `p`-partite graph.
* `erdos_simonovits_stability`. Erdős–Simonovits stability for `K_{p+1}`.

**The regularity method for cliques**

These results extend Mathlib's regularity lemma development, which only covers triangles.

* `card_transversalCliques_ge`, `card_transversalCliques_ge_of_isUniform`,
  `card_cliqueFinset_ge`: the **clique counting lemma**. If `r` parts are pairwise `ε`-uniform with
  density at least `d + ε` and `2rε ≤ d^(r−1)`, then they span at least
  `d^(r choose 2) / 2^r · ∏ |sᵢ|` cliques `K_r`.
* `le_card_cliqueFinset_of_deleteFar`, `clique_removal`: the **clique removal lemma**. A graph
  with fewer than `δ n^r` copies of `K_r` can be made `K_r`-free by deleting fewer than `ε n²`
  edges.
* `exists_embedding`, `exists_embedding_of_isUniform`, `isContained_of_isUniform`: the
  **embedding lemma**. A fixed graph `L` with a proper colouring embeds into pairwise uniform,
  dense, large enough parts, with each vertex mapped into the part of its colour.

**The Erdős–Simonovits stability theorem** (`stability`)

Let `L` be a finite `(p + 1)`-colourable graph. For every `ε > 0` there are `δ > 0` and `n₀` such
that every `L`-free graph on `n ≥ n₀` vertices with at least `(1 − 1/p) n²/2 − δn²` edges differs
from some complete `p`-partite graph in at most `εn²` edges.

A partition into `p` parts is a map `f : V → Fin p`; its complete `p`-partite graph is
`(⊤ : SimpleGraph (Fin p)).comap f`.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`StabilityLib/`](StabilityLib): the proofs.
  - `Furedi.lean`
  - `CliqueCounting.lean`
  - `CliqueRemoval.lean`
  - `Embedding.lean`
  - `StabilityGeneral.lean`
- [`comparator.json`](comparator.json): the 13 theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Füredi's partition inequality.** By induction on `p`:
  1. Take a vertex `x` of maximum degree.
  2. Put its non-neighbours in the first part.
  3. Recurse inside its neighbourhood, which has no `p`-clique.
  4. Every vertex of the first part has degree at most `|N(x)|`; this gives the inequality.
* **From the inequality to the other Füredi statements.** Mathlib's Turán bound
  `CliqueFree.card_edgeFinset_le` gives the remaining statements, and `mul_turanNumber_le` gives
  the asymptotic one.
* **Counting.** By induction on `r`, following Mathlib's triangle counting lemma. Most vertices
  of the first part have the expected number of neighbours in every other part. Their
  neighbourhoods are again robustly dense, and induction applies to them.
* **Removal.** Following Mathlib's triangle removal lemma:
  1. Apply Szemerédi's regularity lemma.
  2. Pass to Mathlib's reduced graph `regularityReduced`, which deletes fewer than `εn²` edges.
  3. An `r`-clique of the reduced graph gives `r` pairwise uniform dense parts.
  4. The counting lemma then gives many `r`-cliques.
* **Embedding.** Greedy. Embed the vertices of `L` one by one, keeping, for each vertex not yet
  embedded, a large set of candidates adjacent to the images of its embedded neighbours.
* **General stability.**
  1. For `n ≥ n₀`, the reduced graph of an `L`-free graph is `K_{p+1}`-free: otherwise the
     embedding lemma puts `L` into `G`.
  2. Füredi's theorem applied to the reduced graph gives a partition.
  3. That partition is within `εn²` of `G`.

## Sources

* Z. Füredi, *A proof of the stability of extremal graphs, Simonovits' stability from Szemerédi's
  regularity*, J. Combin. Theory Ser. B 115 (2015) 66–71, doi:10.1016/j.jctb.2015.05.001.
* M. Simonovits, *A method for solving extremal problems in graph theory, stability problems*, in
  Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic Press (1968) 279–319.
* P. Erdős, *Some recent results on extremal problems in graph theory*, in Theory of Graphs
  (Internat. Sympos., Rome, 1966), Gordon and Breach (1967) 117–123.
* P. Erdős, P. Frankl, V. Rödl, *The asymptotic number of graphs not containing a fixed subgraph
  and a problem for hypergraphs having no exponent*, Graphs Combin. 2 (1986) 113–121,
  doi:10.1007/BF01788085.
* Y. Dillies, B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022, LIPIcs 237,
  9:1–9:19, doi:10.4230/LIPIcs.ITP.2022.9 (Mathlib's regularity lemma, reused here).

## Authorship and use of AI

The author chose the results. The statements and proof plans were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs in five runs, which were audited and rebuilt
locally. Lean checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
