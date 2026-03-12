/-
## Handshaking lemma: the sum of the degrees in a graph is twice the number of its edges

A *simple graph* `G = (V, E)` is defined by its set of *vertices (nodes)* `V` and
a set of *edges* `∅ ⊆ E ⊆ { e = {u, v} ∣ u ≠ v ∈ V }`. It is *finite* if `V` is
finite and its *order* denotes `#V` and *size* denotes `#E`.

The edges can also be interpreted as a relationship `~` between vertices,
where `u ~ v` if and only if `{u, v} ∈ E` (which in particular implies that
`u ≠ v`). Two vertices defining an edge are said to be *adjacent* and an edge
and any of its two vertices are said to be *incident*.

The *neighborhood* of a vertex `v` is defined as `N(v) = {u | u ~ v}`. Its
*degree* `d(v) = #N(v)` is simply the cardinality of its neighborhood.
The *incidence set* of a vertex `v` is defined as `I(v) = {e ∈ E | v ∈ e}`.

**Handshake Lemma.** Given any finite simple graph `G = (V, E)`, the sum of the
degrees of all its vertices equals twice its size, that is `Σ_v d(v) = 2 * #E`.
-/

/-
# Phase 1: Find out as much as is useful about simple graphs in `mathlib`
-/

/-
# Phase 2: Write down the statement of the handshake lemma in lean with `sorry`
-/

/-
# Phase 3: Find a proof of the handshake lemma that you like and flesh it out
-/

/-
# Phase 4: Find out as much as is useful for your proof in `mathlib`
-/

/-
# Phase 5: Implement your fleshed out proof as closely as possible in lean
-/
