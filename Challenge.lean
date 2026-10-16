/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Füredi's stability theorem for Turán's theorem

For a finite simple graph `G` and a map `f : V → Fin p`, the graph
`(⊤ : SimpleGraph (Fin p)).comap f` is the complete `p`-partite graph whose parts are the fibres
of `f`; `G \ (⊤.comap f)` consists of the edges of `G` inside the parts.

* `TuranStability.card_edgeSet_add_le`: **Füredi (2015), partition inequality.** If `G` is
  `K_{p+1}`-free, there is a partition `f` with `e(G) + Σᵢ e(G[Vᵢ]) ≤ e(K(V₁, …, V_p))`.
* `TuranStability.furedi`: **Füredi (2015).** A `K_{p+1}`-free graph with at least
  `turanNumber n p - t` edges has a `p`-partite subgraph with at least `e(G) - t` edges.
* `TuranStability.exists_partition_symmDiff_le`: such a graph is at edit distance at most `3 t`
  from a complete `p`-partite graph, with at most `t` edges inside the parts.
* `TuranStability.erdos_simonovits_stability`: **Erdős–Simonovits stability for cliques.** For
  every `ε > 0` there is `δ > 0` such that every `K_{p+1}`-free graph with at least
  `(1 - 1/p) n² / 2 - δ n²` edges can be turned into a complete `p`-partite graph by changing
  at most `ε n²` edges.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset Fintype SimpleGraph

namespace TuranStability

variable {V : Type*} [Fintype V]

/-- **Füredi's partition inequality.** Every `K_{p+1}`-free finite graph has a partition into
`p` parts (the fibres of `f`) such that the number of edges of `G` plus the number of edges of
`G` inside the parts is at most the number of edges of the complete `p`-partite graph on these
parts. -/
theorem card_edgeSet_add_le {W : Type*} [Finite W] (G : SimpleGraph W) {p : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) :
    ∃ f : W → Fin p, G.edgeSet.ncard + (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤
      ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard := by
  sorry

/-- **Füredi's theorem (2015).** If `G` is a `K_{p+1}`-free graph on `n` vertices with at least
`turanNumber n p - t` edges, then `G` has a `p`-colourable (i.e. `p`-partite) subgraph `H` with
at least `e(G) - t` edges. -/
theorem furedi (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p) (hG : G.CliqueFree (p + 1))
    (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable p ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard + t := by
  sorry

/-- **Füredi's theorem, edit-distance form.** Under the hypotheses of `furedi`, there is a
partition into `p` parts with at most `t` edges of `G` inside the parts, and `G` differs from the
complete `p`-partite graph on these parts in at most `3 t` edges. -/
theorem exists_partition_symmDiff_le (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ f : V → Fin p, (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤ t ∧
      (symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard ≤ 3 * t := by
  sorry

/-- **Erdős–Simonovits stability theorem for cliques** (Erdős 1967, Simonovits 1968), in the
form obtained from Füredi's theorem: for every `ε > 0` there is `δ > 0` such that every
`K_{p+1}`-free graph on `n` vertices with at least `(1 - 1/p) n² / 2 - δ n²` edges differs from
some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem erdos_simonovits_stability {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree (p + 1) →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 := by
  sorry

end TuranStability
