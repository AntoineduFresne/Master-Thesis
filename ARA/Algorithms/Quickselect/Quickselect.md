# Randomized Quickselect

## 1. Problem

Let $(\alpha, \le)$ be a linearly ordered set. Given a finite list
$L \in \alpha^n$ and a rank $k \in \{0, \dots, n-1\}$, compute the
**$k$-th order statistic** $L_{(k)}$: the entry at position $k$
(zero-indexed) of $\mathrm{sort}(L)$. For $k \ge n$ we adopt the
convention that a fixed default element is returned.

## 2. The algorithm

**Randomness model.** As for quicksort: each recursive call on a
sublist of length $m > 0$ draws an independent uniform pivot index in
$\{0, \dots, m-1\}$; the sample space is the finite product of these
uniform draws and the output $\mathrm{QSel}(L, k)$ is a random
variable on it.

**Algorithm** $\mathrm{QSel}(L, k)$:

1. If $L = ()$, return the default element.
2. Otherwise draw $I \sim \mathrm{Unif}\{0, \dots, |L|-1\}$, set
   $p := a_I$, and let $R$ be $L$ with position $I$ removed.
3. Partition $R$ into $L_< := (x \in R : x < p)$ and
   $L_\ge := (x \in R : x \ge p)$ ($|L| - 1$ comparisons).
4. Three cases on $j := |L_<|$:
   * if $k < j$, return $\mathrm{QSel}(L_<, k)$;
   * if $k = j$, return $p$;
   * if $k > j$, return $\mathrm{QSel}(L_\ge, k - j - 1)$.

**Cost model.** As for quicksort: a call at length $m > 0$ costs
$m - 1$ (the comparisons against the pivot), base calls cost $0$;
$C(L,k)$ denotes the (random) total cost.

## 3. Correctness

**Theorem 1 (correctness).** For every $L$ and $k$,
$$\Pr\bigl[\mathrm{QSel}(L, k) = L_{(k)}\bigr] = 1 .$$
The output distribution is the Dirac measure at the $k$-th order
statistic (Las Vegas; for $k \ge n$ both sides are the default
element by convention).

*Proof.* Strong induction on $|L|$. The empty case is the convention.
Otherwise condition on the pivot position; with $p$, $L_<$, $L_\ge$,
$j = |L_<|$ as above, $\mathrm{sort}(L) = \mathrm{sort}(L_<)
\mathbin{+\!\!+} (p) \mathbin{+\!\!+} \mathrm{sort}(L_\ge)$ (as in the
quicksort proof). Reading off position $k$ of this concatenation:

* $k < j$: position $k$ lies in $\mathrm{sort}(L_<)$, so
  $L_{(k)} = (L_<)_{(k)}$, and the recursive call returns it almost
  surely by the induction hypothesis;
* $k = j$: position $j$ is the pivot, so $L_{(k)} = p$;
* $k > j$: position $k$ lies in $\mathrm{sort}(L_\ge)$ at offset
  $k - j - 1$, so $L_{(k)} = (L_\ge)_{(k-j-1)}$, again handled by the
  induction hypothesis. $\blacksquare$

## 4. Complexity

Write $H_n := \sum_{r=1}^n 1/r$.

**Theorem 2 (exact expected cost; Knuth 1971).** If the entries of
$L$ are pairwise distinct, $|L| = n$, and $k < n$, then
$$\mathbb{E}[C(L,k)] \;=\;
  2\Bigl(n + 3 + (n+1)H_n - (k+3)H_{k+1} - (n+2-k)H_{n-k}\Bigr).$$

*Proof.* Identify elements with their ranks $1, \dots, n$ and let
$t := k + 1$ be the one-indexed target rank. For $1 \le i < j \le n$
let $X_{ij}$ indicate that ranks $i$ and $j$ are ever compared, so
$C = \sum_{i<j} X_{ij}$.

*Claim.* With $m := \min(i, t)$ and $M := \max(j, t)$:
$$\Pr[X_{ij} = 1] = \frac{2}{M - m + 1}.$$
Consider the block $B = \{m, \dots, M\}$ of ranks between (the
extremes of) $i, j, t$. As long as no pivot falls in $B$, the entire
block stays in the current sublist: a pivot below $m$ or above $M$
either discards the whole block together with the target — impossible,
the search always keeps the side containing rank $t$ — or keeps it
whole. The first pivot in $B$ is uniform on $B$; ranks $i$ and $j$ are
compared iff it equals $i$ or $j$ (any other choice either separates
$i$ from $j$, or terminates the search at $t$ between them), giving
probability $2/|B|$.

Summing $\Pr[X_{ij}]$ over the three regimes — $t \le i < j$ (block
$\{t,\dots,j\}$), $i < j \le t$ (block $\{i,\dots,t\}$), and
$i < t < j$ (block $\{i,\dots,j\}$) — and evaluating the three double
sums with the standard prefix-sum identities for $\sum H_r$ and
$\sum r H_r$ (stated below) yields the closed form. We omit the
routine summation; the resulting polynomial-harmonic expression is
exactly the displayed formula. $\blacksquare$

**Corollary (minimum selection).** At $k = 0$ the formula collapses to
$$\mathbb{E}[C(L,0)] = 2n - 2H_n .$$

**Theorem 3 (linear bound, distinct elements).** For distinct entries
and any $k$: $\mathbb{E}[C(L,k)] \le 4n$.

*Proof.* By strong induction on $n$, bounding the recurrence: the
call costs $n-1$ and recurses on one side whose expected size,
averaged over the uniform pivot, is at most $\tfrac{3}{4}$-fraction
of $n$ in the amortized sense; concretely, with $E(n) :=
\sup_k \mathbb{E}[C(L,k)]$,
$$E(n) \le (n-1) + \frac{1}{n}\sum_{j=0}^{n-1} E(\max(j, n-1-j)),$$
and $\sum_{j=0}^{n-1} \max(j, n-1-j) \le \tfrac{3}{4} n^2$; unfolding
the induction hypothesis $E(m) \le 4m$ gives
$E(n) \le (n-1) + \frac{1}{n} \cdot 4 \cdot \tfrac{3}{4} n^2 \le 4n$.
$\blacksquare$

**Theorem 4 (quadratic bound, arbitrary lists).** For every list
(duplicates allowed) and every $k$:
$\mathbb{E}[C(L,k)] \le \binom{n}{2}$.

*Proof.* Identical shape to the quicksort quadratic bound: cost
$n - 1$ plus one recursive call on a sublist of total length
$\le n-1$, and $(n-1) + \binom{n-1}{2} = \binom{n}{2}$. $\blacksquare$

## 5. Auxiliary facts used (stated, not proved)

* Reading position $k$ of a sorted concatenation
  $S_1 \mathbin{+\!\!+} (p) \mathbin{+\!\!+} S_2$ gives the three-case
  dispatch above.
* Prefix sums of harmonic numbers:
  $\sum_{r=1}^{m} H_r = (m+1)H_m - m$ and
  $\sum_{r=1}^{m} (r+1)H_r = \frac{(m+1)(m+2)}{2}H_{m+1}
   - \frac{m(m+5)}{4}$ (and the variant for $\sum r H_r$).
* $\sum_{j=0}^{n-1} \max(j, n-1-j) \le \tfrac34 n^2$.
