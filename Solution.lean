/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import StabilityLib.Furedi

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `StabilityLib/Furedi.lean` (namespace `Furedi`), following Füredi
(2015): the partition is built greedily by taking a vertex of maximum degree, putting its
non-neighbours in the first part and recursing inside its neighbourhood (which has no `p`-clique);
comparing the degree sum over the first part with the maximum degree gives the partition
inequality. The remaining statements follow from it and Mathlib's Turán bound
`SimpleGraph.CliqueFree.card_edgeFinset_le`, and, for the asymptotic form, `mul_turanNumber_le`.
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
      ((⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard :=
  Furedi.card_edgeSet_add_le G hp hG

/-- **Füredi's theorem (2015).** If `G` is a `K_{p+1}`-free graph on `n` vertices with at least
`turanNumber n p - t` edges, then `G` has a `p`-colourable (i.e. `p`-partite) subgraph `H` with
at least `e(G) - t` edges. -/
theorem furedi (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p) (hG : G.CliqueFree (p + 1))
    (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable p ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard + t :=
  Furedi.furedi G hp hG ht

/-- **Füredi's theorem, edit-distance form.** Under the hypotheses of `furedi`, there is a
partition into `p` parts with at most `t` edges of `G` inside the parts, and `G` differs from the
complete `p`-partite graph on these parts in at most `3 t` edges. -/
theorem exists_partition_symmDiff_le (G : SimpleGraph V) {p t : ℕ} (hp : 0 < p)
    (hG : G.CliqueFree (p + 1)) (ht : turanNumber (card V) p ≤ G.edgeSet.ncard + t) :
    ∃ f : V → Fin p, (G \ (⊤ : SimpleGraph (Fin p)).comap f).edgeSet.ncard ≤ t ∧
      (symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard ≤ 3 * t :=
  Furedi.exists_partition_symmDiff_le G hp hG ht

/-- **Erdős–Simonovits stability theorem for cliques** (Erdős 1967, Simonovits 1968), in the
form obtained from Füredi's theorem: for every `ε > 0` there is `δ > 0` such that every
`K_{p+1}`-free graph on `n` vertices with at least `(1 - 1/p) n² / 2 - δ n²` edges differs from
some complete `p`-partite graph on the same vertices in at most `ε n²` edges. -/
theorem erdos_simonovits_stability {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Type) [Fintype W] (G : SimpleGraph W), G.CliqueFree (p + 1) →
      (1 - 1 / (p : ℝ)) * (card W : ℝ) ^ 2 / 2 - δ * (card W : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ∃ f : W → Fin p,
        ((symmDiff G ((⊤ : SimpleGraph (Fin p)).comap f)).edgeSet.ncard : ℝ) ≤
          ε * (card W : ℝ) ^ 2 :=
  Furedi.erdos_simonovits_stability hp hε

end TuranStability
