# Karger's Randomized Minimum Cut

## 1. Problem

A **multigraph** $G = (V, E)$ consists of a finite vertex set $V$ and
a finite multiset $E$ of unordered pairs of *distinct* vertices
(parallel edges allowed, no loops). Write $n := |V|$, $m := |E|$
(counted with multiplicity).

*Formalization note.* In Lean an edge is a `Sym2 α` — Mathlib's
unordered pair — and $E$ is a `List (Sym2 α)`, one entry per parallel
copy. Orientation is not merely irrelevant but inexpressible:
`s(u,v)` and `s(v,u)` are the same term. The crossing predicate is
built with `Sym2.lift`, so its symmetry is a *well-definedness
obligation* discharged at definition time, not a theorem proved
afterwards.

This matters, because for *directed* graphs the results below are
false. A digraph can have exponentially many minimum cuts (in the
in-star $v_i \to c$, every $S \ni c$ is a cut of value $0$), and the
key step of Section 4 breaks: a set can have no outgoing edge while
*every* edge is incident on it, so a uniformly random edge merges
across the cut with probability $1$ rather than $\le 2/n$. Note also
that $\deg$ below is the incidence degree, which is why the handshake
identity reads $\sum_v \deg(v) = 2m$ and not $m$.

`Sym2 α` is the endpoint type used by GraphLib (`Edge.endpoints` in
`GraphLib/Graph/Basic.lean`, and `abbrev Edge := Sym2` in Weixuan
Yuan's `UndirectedGraphs/SimpleGraphs.lean`), so this is the graph
notion we intend to import once toolchains align. We diverge on two
points, both forced by executability: multiplicity is carried by
repetition in a `List` rather than by GraphLib's `Edge.edgeLabel` over
a noncomputable `Set` (our `List (Sym2 α)` is their
`Set (Edge α (Fin m))` with the list position as the label), and
contraction merges one endpoint into the other rather than
quotienting the vertex type by a `Setoid`, so that the vertex type is
preserved across the $n-2$ rounds.

## 2. The algorithm

**Contraction.** For an edge $e = \{u, v\} \in E$, the contracted
multigraph $G / e$ has vertex set $V \setminus \{v\}$; every edge
endpoint equal to $v$ is redirected to $u$, and the resulting loops
(the parallel copies of $\{u,v\}$ itself) are deleted. Parallel edges
are **kept**. Thus $|V(G/e)| = n - 1$ and $|E(G/e)| \le m$.

**Randomness model.** Each round draws an edge uniformly from the
current edge multiset, independently across rounds; drawing uniformly
from the multiset makes an edge be picked with probability
proportional to its multiplicity.

**Algorithm** $\mathrm{Karger}(G)$:

1. Repeat $n - 2$ times (stopping early if no edge remains): draw an
   edge $e$ uniformly from the current edge multiset and replace the
   current graph by its contraction along $e$.
2. Return the number of remaining edges.

When no early stop occurs, two supervertices remain; each
supervertex is a set of original vertices, and the surviving edges
are exactly the original edges crossing that two-set partition — so
the returned number is the value of a cut of $G$.

**Cost model.** Each contraction round costs the number of edges of
the current graph (the pass that redirects and filters the edge
list); $C(G)$ is the total (random) cost.

## 3. Correctness (one-sided error)

**Lemma 1 (cut lifting).** Every cut of $G/e$ is a cut of $G$ of the
same value. Consequently $\lambda(G/e) \ge \lambda(G)$.

*Proof.* Let $e = \{u,v\}$ and let $S'$ be a cut of $G/e$. If
$u \notin S'$, take $S := S'$; if $u \in S'$, take
$S := S' \cup \{v\}$. In both cases $u$ and $v$ lie on the same side
of $S$, so redirection does not change which edges cross, and deleted
loops (copies of $\{u,v\}$) never cross: $w_G(S) = w_{G/e}(S')$. Both
sides of $S$ are nonempty because both sides of $S'$ are.
$\blacksquare$

**Theorem 1 (never undershoots).** Every value the algorithm can
output is $\ge \lambda(G)$: for all $c$,
$$\Pr[\mathrm{Karger}(G) = c] > 0 \implies c \ge \lambda(G).$$

*Proof.* By induction on the number of rounds, using Lemma 1: the
minimum cut value never decreases under contraction, and at the end
the output is the value of some cut of the final graph, hence
$\ge \lambda(\text{final}) \ge \lambda(G)$. (If the edge multiset
becomes empty early, the graph has a cut of value $0$, the output is
$0 = \lambda(G)$.) $\blacksquare$

## 4. Success probability

**Lemma 2 (degree bound).** For $n \ge 2$, every vertex degree is
$\ge \lambda(G)$, since the singleton $\{v\}$ is a cut of value
$\deg(v)$. By the handshake identity $\sum_v \deg(v) = 2m$,
$$n \,\lambda(G) \le 2m .$$

**Lemma 3 (cut survival).** If $S$ is a cut of $G$ and $e$ does not
cross $S$, then (the image of) $S$ is a cut of $G/e$ with the same
value. Together with Lemma 1: contracting a non-crossing edge
preserves $\lambda$ exactly when $S$ is minimum.

**Theorem 2 (success probability).** For $n \ge 2$,
$$\Pr\bigl[\mathrm{Karger}(G) = \lambda(G)\bigr]
 \;\ge\; \frac{2}{n(n-1)} .$$

*Proof.* Fix a minimum cut $S$, $w(S) = \lambda =: c$. We show by
induction on $n$ that the $n-2$ contraction rounds avoid all $c$
crossing edges of $S$ — and then the final two-vertex graph reports
exactly $c$ — with probability at least $2/(n(n-1))$.

*Base $n = 2$:* no rounds; every edge crosses every cut, so the edge
count *is* $\lambda(G)$; probability $1 \ge 2/(2\cdot 1)$.

*Step, $n \ge 3$, current graph $G'$ with $\lambda(G') = \lambda$ and
$m'$ edges:* if $m' = 0$ then $\lambda = 0$ and the output is exact.
Otherwise a uniformly random edge crosses $S$ with probability
$c / m' \le 2/n$ by Lemma 2 applied to $G'$
($c \, n \le 2 m'$). Conditioned on a non-crossing draw, Lemma 3
keeps $S$ a minimum cut of the contracted graph on $n - 1$ vertices,
and the induction hypothesis applies. Hence
$$\Pr[\text{success}] \ \ge\
  \Bigl(1 - \frac{2}{n}\Bigr)\cdot\frac{2}{(n-1)(n-2)}
  \ =\ \frac{n-2}{n}\cdot\frac{2}{(n-1)(n-2)}
  \ =\ \frac{2}{n(n-1)} . \qquad\blacksquare$$

## 5. Amplification

Because the algorithm never undershoots (Theorem 1), taking the
**minimum over $k$ independent runs** succeeds as soon as any single
run does.

**Theorem 3 (amplified success).** For $n \ge 2$ and $k \ge 1$
independent runs, with $p := 2/(n(n-1))$:
$$\Pr\Bigl[\min_{1 \le i \le k} \mathrm{Karger}_i(G) = \lambda(G)\Bigr]
 \;\ge\; 1 - (1 - p)^k .$$

*Proof.* Every run outputs a value $\ge \lambda(G)$ almost surely, so
the minimum equals $\lambda(G)$ iff at least one run outputs
$\lambda(G)$. The runs are independent and each fails with
probability $\le 1 - p$, so all fail with probability
$\le (1-p)^k$. $\blacksquare$

In particular $k = \Theta(n^2 \log n)$ repetitions drive the failure
probability below any fixed inverse polynomial, using
$1 - x \le e^{-x}$.

## 6. Complexity

**Theorem 4 (expected cost).** For every input,
$$\mathbb{E}[C(G)] \;\le\; (n-2)\, m,$$
and $k$ amplified runs cost at most $k (n-2) m$ in expectation.

*Proof.* Contraction never increases the edge count, so each of the
at most $n - 2$ rounds costs at most $m$; sum and take expectations.
Amplification is linear by independence and linearity of
expectation. $\blacksquare$

## 7. Auxiliary facts used (stated, not proved)

* Handshake identity: $\sum_{v \in V} \deg(v) = 2m$ in a loopless
  multigraph.
* In a two-vertex loopless multigraph every edge crosses the unique
  (up to complement) cut.
* $\prod_{i=0}^{n-3}\bigl(1 - \tfrac{2}{n-i}\bigr) = \tfrac{2}{n(n-1)}$
  (the telescoping product behind the induction).
