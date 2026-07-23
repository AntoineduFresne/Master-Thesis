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
contraction works on **supervertices** — the working graph's vertices
are the sets of original vertices merged so far, and contracting an
edge unites its two endpoints — rather than quotienting the vertex
type by a `Setoid`. The union of sets is symmetric, so contraction is
a genuine function of the *unordered* edge (no orientation, no
tie-break), and the vertex type is preserved across the $n-2$ rounds.

## 2. The algorithm

**Contraction.** The working graph's vertices are **supervertices**:
pairwise-disjoint nonempty sets of original vertices, initially the
singletons $\{v\}$, $v \in V$. For an edge $e = \{S, T\}$ of the
working graph, the contracted multigraph $G / e$ replaces the two
supervertices $S$ and $T$ by their union $S \cup T$; every edge
endpoint equal to $S$ or $T$ is redirected to $S \cup T$, and the
resulting loops (the parallel copies of $\{S,T\}$ itself) are
deleted. Parallel edges are **kept**. Merging is symmetric in $S$ and
$T$, and by disjointness the union is a *new* supervertex, so
$|V(G/e)| = |V(G)| - 1$ and $|E(G/e)| \le |E(G)|$.

**Randomness model.** Each round draws an edge uniformly from the
current edge multiset, independently across rounds; drawing uniformly
from the multiset makes an edge be picked with probability
proportional to its multiplicity.

**Algorithm** $\mathrm{Karger}(G)$:

1. Repeat $n - 2$ times (stopping early if no edge remains): draw an
   edge $e$ uniformly from the current edge multiset and replace the
   current graph by its contraction along $e$.
2. Return the **partition** $\{S, \bar S\}$ formed by the surviving
   supervertices, together with its value: each remaining supervertex
   is the set of original vertices merged into it — one side of the
   cut — and $c$ is the number of remaining edges.

When two supervertices remain the surviving edges are exactly the
original edges crossing that two-set partition — so the reported $c$
*is* $w(S)$ for each side $S$ (Lemma 1' below), computed for free
rather than recounted. The analysis inducts on the minimum-cut value
of the working graph and the bridge promotes every statement about it
to a statement about the returned sides themselves.

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

**Theorem 1 (the output is a cut).** On every run the output
$(\{S, \bar S\}, c)$ satisfies: each side is a genuine cut of $G$
($\emptyset \ne S \subsetneq V$), $c = w(S)$ for each side, and
$c \ge \lambda(G)$ — the algorithm never undershoots.

**Lemma 1' (the bridge).** Throughout a run the supervertices form a
partition of $V$ into nonempty parts, and every cut $\mathcal{S}$ of
the working graph flattens (take the union of its supervertices) to a
cut of $G$ of the *same value*. Consequently
$$w(S) = c$$
on every run and for each returned side $S$: the returned cut has
exactly the value the run reports.

*Proof.* Induction on the rounds. The base case is the singleton
partition. For the step, contracting $\{S,T\}$ replaces the parts
$S, T$ by $S \cup T$, which preserves the partition property (by
disjointness) and the flattening of any cut. At the end two
supervertices remain, so by Section 2 every cut of the final graph
has value equal to its edge count. $\blacksquare$

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

**Theorem 2 (success probability).** For $n \ge 2$, the algorithm
returns an actual *minimum cut* — both sides of the returned
partition are cuts of value exactly $\lambda(G)$ — with probability
$$\Pr\bigl[w(\mathrm{Karger}(G)) = \lambda(G)\bigr]
 \;\ge\; \frac{2}{n(n-1)} .$$
By Lemma 1' it suffices to prove the same bound for the reported
value $c$, which is what the induction below does.

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

**Theorem 2' (partial contraction).** The induction proves more: for
any target $2 \le t \le n$, stopping after $n - t$ rounds leaves a
working graph on $t$ supervertices whose minimum-cut value still
equals $\lambda(G)$ with probability at least
$$\frac{t(t-1)}{n(n-1)}
 \;=\; \prod_{i=0}^{n-t-1}\Bigl(1 - \frac{2}{n-i}\Bigr).$$
Theorem 2 is the case $t = 2$; the case $t = \lceil 1 + n/\sqrt2\,\rceil$,
where the bound is $\ge 1/2$, is the step Karger–Stein recurses on.

## 5. Amplification

Because the algorithm never undershoots (Theorem 1), taking the
**minimum over $k$ independent runs** succeeds as soon as any single
run does.

**Theorem 3 (amplified success).** For $n \ge 2$ and $k \ge 1$
independent runs, with $p := 2/(n(n-1))$, keeping the run whose cut has
the smallest value:
$$\Pr\Bigl[\min_{1 \le i \le k} c_i = \lambda(G)\Bigr]
 \;\ge\; 1 - (1 - p)^k ,$$
where $(S_i, c_i)$ is the output of run $i$ and the kept pair is the
one with smallest $c_i$ (no recomputation: $c_i$ is already there).

*Proof.* Every run outputs a cut, hence a value $\ge \lambda(G)$, so
the kept cut has value $\lambda(G)$ iff at least one run achieves it. The runs are independent and each fails with
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
