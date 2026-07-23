# The Karger–Stein Recursive Contraction Algorithm

## 1. Problem

As for Karger's algorithm: a loopless multigraph $G = (V, E)$ with
$n := |V|$ vertices and $m := |E|$ edges (with multiplicity), and the
goal of finding a global minimum cut, of value $\lambda(G)$.

A single contraction run succeeds with probability only
$\Theta(1/n^2)$, so plain repetition needs $\Theta(n^2 \log n)$ runs.
The key observation of Karger–Stein: the run's *early* contractions
are nearly safe (the first step destroys the minimum cut with
probability only $\le 2/n$), and only the *late* ones are risky. So:
contract slowly down to $\approx n/\sqrt2$ vertices — this preserves
the minimum cut with probability $\ge 1/2$ — and spend the repetition
budget on the risky small graphs, by recursing **twice** and keeping
the better answer.

## 2. The algorithm

**The contraction target.** For $n \ge 2$ let
$$t(n) \;:=\; \min\,\{\, t \ge 2 \;:\; 2\,t(t-1) \,\ge\, n(n-1) \,\},$$
the number of supervertices at which the survival probability of a
fixed minimum cut first reaches $1/2$ (Theorem 1). Classically one
writes $t(n) = \lceil 1 + n/\sqrt2\,\rceil$; the integer
characterization above is equivalent for the analysis, avoids
irrational arithmetic entirely, and is executable. It satisfies
$t(n) < n$ exactly when $n \ge 4$ (for $t = n-1$:
$2(n-1)(n-2) \ge n(n-1) \iff n \ge 4$), which delimits the base case.

**Algorithm** $\mathrm{KS}(G)$:

1. If $n \le 3$: contract down to $2$ supervertices (Karger's single
   run) and return the resulting partition with its value.
2. Otherwise, **twice and independently**: contract the current graph
   down to $t(n)$ supervertices, and recurse on the result.
3. Of the two returned outputs, keep the one with the smaller
   reported value.

Contraction, the supervertex model, the partition output and the cost
model (each contraction round costs the current number of edges) are
exactly as in `Karger.md` §2.

**Recursion depth.** Define $d(2) = d(3) = 0$ and
$d(n) = 1 + d(t(n))$ for $n \ge 4$ (well-founded since $t(n) < n$).

## 3. Survival of the minimum cut (proved for Karger)

**Theorem 1 (partial contraction).** For a working graph on
$n = k + t$ supervertices with $t \ge 2$, the $k$ contraction rounds
preserve the minimum-cut value with probability at least
$$\frac{t(t-1)}{n(n-1)}
  \;=\; \prod_{i=0}^{k-1}\Bigl(1 - \frac{2}{n-i}\Bigr).$$

This is Karger's Theorem 2′ (`Karger.md`), the shared kernel of both
analyses; in the formal development it is one statement
(`success_contractAux`), with Karger's $2/(n(n-1))$ the case $t = 2$.

**Corollary (half survival).** By the definition of $t(n)$,
contracting from $n$ to $t(n)$ vertices preserves the minimum-cut
value with probability
$$\frac{t(n)(t(n)-1)}{n(n-1)} \;\ge\; \frac12 .$$

## 4. Success probability

Both branches of the recursion never undershoot (`Karger.md`
Theorem 1 applies verbatim: every output value is the value of a
genuine cut, hence $\ge \lambda$), so **keeping the better of two
runs succeeds as soon as either does** — the same one-sidedness that
drives plain amplification.

**Theorem 2 (success).** For every $n \ge 2$,
$$\Pr\bigl[\mathrm{KS}(G) \text{ reports } \lambda(G)\bigr]
  \;\ge\; \frac{1}{d(n) + 3},$$
and each reported side is then a genuine minimum cut, as in Karger's
Theorem 2.

*Proof.* Induction on the recursion. Base $n \le 3$: a full
contraction succeeds with probability $\ge 2/(n(n-1)) \ge 1/3
= 1/(0+3)$.

Step $n \ge 4$: write $p := \Pr[\mathrm{KS}(\text{graph on } t(n))
\text{ succeeds}] \ge 1/(d(t(n))+3) =: x$ by the induction
hypothesis. One branch succeeds when the partial contraction
preserves the minimum cut (prob. $\ge 1/2$, Corollary) *and* the
recursive call then succeeds on a graph whose minimum-cut value still
equals $\lambda(G)$ (prob. $\ge p$, independence): so each branch
succeeds with probability $q \ge p/2$. By one-sidedness the better of
the two independent branches fails only if both fail:
$$\Pr[\text{success}] \;\ge\; 1 - (1 - q)^2 \;\ge\; 1 - \Bigl(1 -
\frac{x}{2}\Bigr)^2 \;=\; x - \frac{x^2}{4}.$$
Finally, with $x \ge 1/(d+3)$ where $d := d(t(n))$,
$$x - \frac{x^2}{4} \;\ge\; \frac{1}{d+3} - \frac{1}{4(d+3)^2}
  \;\ge\; \frac{1}{d+4}
  \;=\; \frac{1}{d(n)+3},$$
the middle inequality because
$\tfrac1{d+3} - \tfrac1{d+4} = \tfrac1{(d+3)(d+4)} \ge
\tfrac1{4(d+3)^2} \iff 4(d+3) \ge d+4$. $\blacksquare$

**Corollary (logarithmic success).** With the depth bound of §6,
$$\Pr[\mathrm{KS}(G) \text{ reports } \lambda(G)]
  \;\ge\; \frac{1}{2\lceil \log_2 n\rceil + 3}
  \;=\; \Omega\!\Bigl(\frac{1}{\log n}\Bigr).$$
Repeating $\mathrm{KS}$ independently $\Theta(\log^2 n)$ times and
keeping the best output therefore finds a minimum cut with high
probability, at which point the failure product argument of
`Karger.md` §5 applies verbatim (one-sidedness again).

## 5. Complexity

**Theorem 3 (expected cost, list model).** In the cost model of
`Karger.md` §2 (each contraction round costs the current edge count),
$$\mathbb{E}[C(G)] \;\le\; 7\, n^2 m .$$

*Proof sketch.* Edge counts never increase along a recursion path, so
every round costs at most $m$, and a call at size $n_i$ performs at
most $n_i$ rounds before recursing. The recursion tree has $2^i$
calls at level $i$, of size $n_i \le n/(\sqrt2)^{\,i} + O(1)$, so
level $i$ costs at most $2^i \, n_i\, m \approx n\,m\,(\sqrt2)^{\,i}$;
the geometric sum is dominated by the last level $i = d(n) \le
2\lceil\log_2 n\rceil$, where $(\sqrt2)^{\,d(n)} \le 2n$, giving
$\sum_i n\,m\,(\sqrt2)^i \le \tfrac{2\sqrt2}{\sqrt2 - 1}\, n^2 m
\le 7\,n^2 m$. $\blacksquare$

*Remark (model).* The classical $O(n^2 \log^2 n)$-work-per-success
headline assumes an $O(n)$-per-contraction implementation (adjacency
matrices), under which a call at size $n_i$ costs $O(n_i^2)$ and each
level of the tree costs $O(n^2)$, giving $O(n^2 \log n)$ per run. Our
edge-list cost model charges a full list pass per round; the honest
bound in that model is the $O(n^2 m)$ above. The two models differ
only in the per-round charge, not in the probabilistic analysis.

## 6. Auxiliary facts used (stated, not proved)

* **Depth bound**: $d(n) \le 2\lceil \log_2 n \rceil$ for all
  $n \ge 2$. (Two levels of $t(\cdot)$ at least halve $n$, up to the
  additive constant absorbed by the ceiling; verified numerically for
  $n \le 300$.)
* $t(n) < n$ for $n \ge 4$, and $2\,t(n)(t(n)-1) \ge n(n-1)$ by
  definition.
* $\tfrac1{d+3} - \tfrac1{4(d+3)^2} \ge \tfrac1{d+4}$ for all
  $d \ge 0$ (used in Theorem 2).
* Independence of the two recursive branches, and of the rounds
  within a contraction pass.
