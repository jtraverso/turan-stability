# Füredi's stability theorem for Turán's theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Turán's theorem (in Mathlib) says that a graph on `n` vertices without a clique `K_{p+1}` has at
most `t(n, p)` edges, the number of edges of the Turán graph. This repository formalizes the
corresponding **stability** results, which are not in Mathlib:

1. **Füredi's partition inequality** (`TuranStability.card_edgeSet_add_le`). Every
   `K_{p+1}`-free finite graph `G` has a partition `V₁, …, V_p` of its vertices with
   `e(G) + Σᵢ e(G[Vᵢ]) ≤ e(K(V₁, …, V_p))`, where `K(V₁, …, V_p)` is the complete `p`-partite graph
   on these parts.
2. **Füredi's theorem (2015)** (`TuranStability.furedi`). If `G` is `K_{p+1}`-free with at least
   `t(n, p) − t` edges, then `G` has a `p`-partite subgraph with at least `e(G) − t` edges: it can
   be made `p`-partite by deleting at most `t` edges.
3. **Edit-distance form** (`TuranStability.exists_partition_symmDiff_le`). Under the same
   hypotheses there is a partition with at most `t` edges of `G` inside the parts, and `G` differs
   from the complete `p`-partite graph on it in at most `3t` edges.
4. **Erdős–Simonovits stability theorem for cliques**
   (`TuranStability.erdos_simonovits_stability`). For every `ε > 0` there is `δ > 0` such that
   every `K_{p+1}`-free graph on `n` vertices with at least `(1 − 1/p) n²/2 − δn²` edges differs
   from some complete `p`-partite graph in at most `εn²` edges.

A partition into `p` parts is a map `f : V → Fin p`; its complete `p`-partite graph is
`(⊤ : SimpleGraph (Fin p)).comap f`. Edge counts are `Set.ncard` of `edgeSet`.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`StabilityLib/Furedi.lean`](StabilityLib/Furedi.lean):
  the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Partition inequality.** By induction on `p`, inside an arbitrary vertex set `S`:
  1. Take a vertex `x` of maximum degree in `S`.
  2. Let `V₁` be its non-neighbours in `S` (including `x`) and `N` its neighbourhood in `S`.
  3. `N` has no `p`-clique, so by induction it has a partition into `p − 1` parts satisfying the
     inequality.
  4. Every vertex of `V₁` has degree at most `|N|`, so `2e(G[V₁]) + e(V₁, N) ≤ |V₁||N|`. Adding
     this to the inductive inequality gives the claim for `S`.
* **Füredi's theorem and the edit-distance form.** The complete `p`-partite graph is
  `K_{p+1}`-free, so by Mathlib's Turán bound (`SimpleGraph.CliqueFree.card_edgeFinset_le`) it has
  at most `t(n, p)` edges. Combined with the partition inequality, this bounds the edges inside
  the parts by `t` and the missing edges by `2t`.
* **Erdős–Simonovits.** Take `δ = ε/3`. Then `t(n, p) ≤ (1 − 1/p) n²/2` by Mathlib's
  `mul_turanNumber_le`, and the edit-distance form gives the result.

The paper also derives the stability theorem for every forbidden graph `L` with `χ(L) = p + 1`,
using the removal lemma. That case is not formalized here: Mathlib has the removal lemma only for
triangles.

## Sources

* Z. Füredi, *A proof of the stability of extremal graphs, Simonovits' stability from Szemerédi's
  regularity*, J. Combin. Theory Ser. B 115 (2015) 66–71, doi:10.1016/j.jctb.2015.05.001.
* M. Simonovits, *A method for solving extremal problems in graph theory, stability problems*, in
  Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic Press (1968) 279–319.
* P. Erdős, *Some recent results on extremal problems in graph theory*, in Theory of Graphs
  (Internat. Sympos., Rome, 1966), Gordon and Breach (1967) 117–123.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
