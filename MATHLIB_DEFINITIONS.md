# Mathlib definitions used in Challenge.lean (Füredi and Erdős–Simonovits stability)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## Lattice operations on SimpleGraph (⊤ is the complete graph)

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 311:

```lean
instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SimpleGraph V) where
  top.Adj := Ne
  bot.Adj _ _ := False
  le_top x _ _ h := x.ne_of_adj h
  bot_le _ _ _ h := h.elim
  sdiff_eq x y := by
    ext v w
    refine ⟨fun h => ⟨h.1, ⟨?_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rintro rfl
    exact x.irrefl h.1
  inf_compl_le_bot _ _ _ h := False.elim <| h.2.2 h.1
  top_le_sup_compl G v w hvw := by
    by_cases h : G.Adj v w
    · exact Or.inl h
    · exact Or.inr ⟨hvw, h⟩
  isLUB_sSup _ := ⟨fun G hG _ _ hab ↦ ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ ↦ hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab ↦ hab.1 hG, fun _ hG _ _ hab ↦ ⟨fun _ hH => hG hH hab, hab.ne⟩⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]
```

## SimpleGraph.top_adj

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 338:

```lean
@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
```

## SimpleGraph difference

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 260:

```lean
/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj
      symm.symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }
```

## SimpleGraph supremum

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 228:

```lean
/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (SimpleGraph V) where
  max x y :=
    { Adj := x.Adj ⊔ y.Adj
      symm.symm v w h := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }
```

## symmDiff

`Mathlib/Order/SymmDiff.lean`, line 68:

```lean
def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a
```

## SimpleGraph.edgeSetEmbedding

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 477:

```lean
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩
```

## SimpleGraph.edgeSet

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 483:

```lean
/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G
```

## SimpleGraph.edgeFinset

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 59:

```lean
/-- The `edgeSet` of the graph as a `Finset`. -/
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet
```

## Set.encard

`Mathlib/Data/Set/Card.lean`, line 67:

```lean
/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
```

## Set.ncard

`Mathlib/Data/Set/Card.lean`, line 613:

```lean
/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard
```

## SimpleGraph.comap

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 126:

```lean
/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`). -/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
```

## SimpleGraph.IsClique

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 48:

```lean
/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
```

## SimpleGraph.IsNClique

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 246:

```lean
/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
```

## SimpleGraph.CliqueFree

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 379:

```lean
/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
```

## SimpleGraph.cliqueFinset

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 854:

```lean
/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNClique n s}
```

## SimpleGraph.Coloring

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 74:

```lean
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## SimpleGraph.Colorable

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 163:

```lean
/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))
```

## SimpleGraph.Hom

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 293:

```lean
/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
```

## RelHom

`Mathlib/Order/RelIso/Basic.lean`, line 46:

```lean
/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)
```

## SimpleGraph.Copy

`Mathlib/Combinatorics/SimpleGraph/Copy.lean`, line 84:

```lean
/-- The type of copies as a subtype of *injective* homomorphisms. -/
structure Copy (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : H →g G
  injective' : Injective toHom
```

## SimpleGraph.IsContained

`Mathlib/Combinatorics/SimpleGraph/Copy.lean`, line 239:

```lean
/-- The relation `IsContained H G`, `H ⊑ G` says that `G` contains a copy of `H`.

This is equivalent to the existence of an isomorphism from `H` to a subgraph of `G`. -/
abbrev IsContained (H : SimpleGraph W) (G : SimpleGraph V) := Nonempty (Copy H G)
```

## SimpleGraph.turanGraph

`Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean`, line 63:

```lean
/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r
```

## SimpleGraph.turanNumber

`Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean`, line 330:

```lean
/-- The number of edges in `turanGraph n r`. -/
abbrev turanNumber (n r : ℕ) : ℕ := #(turanGraph n r).edgeFinset
```

## Rel.interedges

`Mathlib/Combinatorics/SimpleGraph/Density.lean`, line 49:

```lean
/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s : Finset α) (t : Finset β) : Finset (α × β) := {e ∈ s ×ˢ t | r e.1 e.2}
```

## Rel.edgeDensity

`Mathlib/Combinatorics/SimpleGraph/Density.lean`, line 52:

```lean
/-- Edge density of a relation between two finsets of vertices. -/
def edgeDensity (s : Finset α) (t : Finset β) : ℚ := #(interedges r s t) / (#s * #t)
```

## SimpleGraph.interedges

`Mathlib/Combinatorics/SimpleGraph/Density.lean`, line 280:

```lean
/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s t : Finset α) : Finset (α × α) :=
  Rel.interedges G.Adj s t
```

## SimpleGraph.edgeDensity

`Mathlib/Combinatorics/SimpleGraph/Density.lean`, line 284:

```lean
/-- Density of edges of a graph between two finsets of vertices. -/
def edgeDensity : Finset α → Finset α → ℚ :=
  Rel.edgeDensity G.Adj
```

## SimpleGraph.IsUniform

`Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean`, line 61:

```lean
/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (#s : 𝕜) * ε ≤ #s' →
    (#t : 𝕜) * ε ≤ #t' → |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
deriving Decidable
```

## SimpleGraph.deleteEdges

`Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean`, line 46:

```lean
/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s
```

## SimpleGraph.DeleteFar

`Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean`, line 222:

```lean
/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ #s
```

## Fintype.piFinset

`Mathlib/Data/Fintype/Pi.lean`, line 32:

```lean
/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩
```
