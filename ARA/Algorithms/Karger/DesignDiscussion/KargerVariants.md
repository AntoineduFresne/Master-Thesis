# Karger under four contraction models

Karger's algorithm is "contract random edges until two vertices
remain". But *what is contraction, concretely?* Contracting an edge
must replace its two endpoints by a single merged vertex, and since
the edge is unordered, the merged vertex must be chosen **symmetrically
in the two endpoints**. This folder runs Karger under every such
choice and proves, for the three representative-style rules, that the
entire analysis — correctness, success probability, expected cost —
is a function of one datum: the merge rule.

## The four models

Let $e = \{u, v\}$ be the contracted edge of the current graph $G$.

1. **Order.** The vertices carry a linear order; merge into
   $\min(u,v)$. Symmetric because $\min$ is commutative.
2. **Enumeration.** An injective labeling $\ell$ of the vertices is
   fixed *once, as input*; merge into the endpoint of smaller label.
   Symmetric *because $\ell$ is injective* — a tie is impossible
   unless $u = v$.
3. **Fresh vertex.** Delete both endpoints and glue their edges to a
   brand-new vertex $w \notin V(G)$. Trivially symmetric — $w$
   mentions neither endpoint.
4. **Supervertex** (the design narrative of `Variants.lean`; the main
   Karger file runs models 1–3 through an abstract pick). Vertices are
   *sets* of original vertices; merge into the union $u \cup v$.
   Symmetric because $\cup$ is commutative.

All four are instances of one **rename contraction**: the endpoints
leave the vertex set, a single vertex $w$ enters, every edge is
redirected through the merge ($u \mapsto w$, $v \mapsto w$, all else
fixed), and the loops this creates — the parallel copies of $e$ — are
dropped.

## One freshness condition carries the whole theory

**Claim.** For every statement below, the *only* property of the
choice of $w$ that matters is:

> $w$ is not an untouched vertex: $w \notin V(G) \setminus \{u, v\}$.

Given this, for a well-formed multigraph (edges have their endpoints
in $V$, no self-loops):

* **Cardinality.** $|V(G/e)| = |V(G)| - 1$: two vertices leave, one
  fresh vertex enters.
* **Cut lifting** (soundness). Every cut $S'$ of $G/e$ pulls back to a
  cut $S$ of $G$ with the same value: take
  $S = \{x \in V(G) : x\text{'s image lies in } S'\}$. Crossing edges
  correspond bijectively — a dropped loop never crosses, a kept edge
  crosses $S'$ iff its preimage crosses $S$. Hence
  $\mu(G/e) \ge \mu(G)$ when $|V(G)| \ge 3$ ($G/e$ must still have a
  cut), where $\mu$ is the minimum-cut value.
* **Cut survival.** If a cut $S$ of $G$ is not crossed by $e$, its
  merge-image is a cut of $G/e$ of the same value ($w$ joins the image
  iff both endpoints lay in $S$; freshness keeps the image proper).
  Consequently, contracting an edge that avoids a fixed minimum cut
  **preserves** $\mu$ exactly.

Models 1 and 2 satisfy freshness because the merged vertex *is* one of
the endpoints; model 3 by construction of the supply; model 4 because
the supervertices are pairwise disjoint, so a union can never equal an
untouched supervertex.

## The shared algorithm and its theorems

Let $n = |V(G)|$, $m$ the number of edges. Draw a uniformly random
edge (parallel edges counted with multiplicity), contract it by the
rule, repeat for $n - 2$ rounds (stopping early if no edge is left),
and report the number of surviving parallel edges — the value of the
cut found. The round count is declared up front, which is why the
cost bound below holds without well-formedness; on a well-formed
input the rounds end exactly when two vertices remain. For **every** merge rule satisfying the freshness condition:

* **One-sided error.** Every reported value is $\ge \mu(G)$. *Proof:*
  by cut lifting, $\mu$ only grows along a run; a final two-vertex
  graph is well-formed and loopless, so all surviving edges join the
  same pair — the edge count is the value of its (unique, up to
  complement) cut, which is at least the final $\mu$.
* **Success probability.**
  $$\Pr[\text{reported value} = \mu(G)] \;\ge\; \frac{2}{n(n-1)}.$$
  *Proof:* fix a minimum cut $S$ with $c$ crossing edges. Every vertex
  has degree $\ge c$ (else its singleton beats $S$), so
  $c \cdot n \le 2m$ by the handshake identity: a uniform edge crosses
  $S$ with probability at most $2/n$. Surviving all $n-2$ rounds
  happens with probability at least
  $\prod_{i=0}^{n-3}\left(1 - \frac{2}{n-i}\right) = \frac{2}{n(n-1)}$,
  and on survival the final value is exactly $\mu(G)$ by cut survival.
  (The formal induction proves the generalized statement: contracting
  from $k + s + 2$ down to $s + 2$ vertices preserves $\mu$ with
  probability at least $\frac{(s+2)(s+1)}{(k+s+2)(k+s+1)}$.)
* **Amplification.** The smallest of $k$ independent reported values
  equals $\mu(G)$ with probability at least
  $1 - \left(1 - \frac{2}{n(n-1)}\right)^k$ — one-sided error makes
  $\min$ the right combiner.
* **Expected cost.** With one tick per edge scanned during a
  contraction pass, a run costs at most $(n-2)\,m$ in expectation, for
  arbitrary (even ill-formed) inputs: at most $n-2$ passes, each over
  at most $m$ edges, since contraction never adds an edge.

## What distinguishes the models

The theorems above are identical across models. The differences are
**where the hypotheses live and what the algorithm can output**:

|                          | Order | Enumeration | Fresh | Supervertex |
|--------------------------|-------|-------------|-------|-------------|
| assumption on vertices   | linear order | none (labeling is data) | a name supply | none |
| what threads through statements | the order, everywhere | the labeling, everywhere | the supply | nothing |
| freshness obligation     | trivial | trivial | genuine proof | disjointness invariant |
| well-defined on unordered edge | commutativity | **injectivity of the labeling** | trivial | commutativity |
| output                   | value only | value only | value only | **the cut itself** + value |

* The **order** model's hypothesis has no mathematical content — the
  min-cut problem does not care that vertices are comparable.
* The **enumeration** model moves the order out of the type and into
  the input: better hygiene, same ceremony — every statement now
  mentions a labeling the output does not depend on. (A labeling also
  orients every edge, low label → high label; cut values are
  orientation-invariant, which is why the unordered-edge treatment is
  sound.)
* The **fresh** model is the tempting one: erase both endpoints, glue
  everyone to a new vertex. *Nothing breaks in the recursion* — the
  analysis above applies verbatim. The costs are elsewhere. First, the
  supply: for an arbitrary vertex type, fresh names require an
  infinite type and a choice function — not executable; concretely one
  fixes the vertices to be numbers and picks $\max + 1$, which is an
  order in disguise. Second, anonymity: the new vertex forgets which
  vertices it swallowed, so the run's final two vertices are
  meaningless names and only the cut *value* can be reported;
  recovering the cut itself would require carrying a representative
  map through the whole recursion.
* The **supervertex** model is the fresh model with the one canonical
  new-vertex choice that needs no supply and forgets nothing:
  $w = u \cup v$. The "representative map" becomes the identity — a
  vertex *is* the set of original vertices merged into it — so the
  final two vertices literally *are* the two sides of the cut, and the
  freshness condition is discharged by the disjointness of the
  supervertices. This is why the supervertex model needs no separate
  representative map — and why `Karger.lean` instead threads `rep`
  explicitly, which lets every rename model state the textbook theorem
  ("the algorithm finds a minimum **cut**"); `KargerVariants.lean`
  keeps the value-level shadow.

## Statements proved (constants as in the Lean files)

For each rule $R \in \{\text{order}, \text{enum}, \text{fresh}\}$ and
well-formed $G$ with $n \ge 2$:

1. every supported output $x$ satisfies $\mu(G) \le x$;
2. $\dfrac{2}{n(n-1)} \le \Pr[\text{output} = \mu(G)]$;
3. $1 - \left(1 - \dfrac{2}{n(n-1)}\right)^k \le
   \Pr[\min \text{ of } k \text{ runs} = \mu(G)]$;
4. expected cost $\le (n-2)\,m$ (no well-formedness needed).

The generic development proves these once, from the freshness
condition alone; each model contributes only its merge rule and the
discharge of that condition.
