# Randomized Quicksort

## 1. Problem

Let $(\alpha, \le)$ be a linearly ordered set. Given a finite list
$L = (a_0, \dots, a_{n-1}) \in \alpha^n$, produce the (unique)
sorted list $\mathrm{sort}(L)$: the list $(b_0, \dots, b_{n-1})$ such
that $b_0 \le b_1 \le \dots \le b_{n-1}$ and $(b_i)$ is a permutation
of $(a_i)$ — formally, the two lists are equal as multisets, and any
two sorted lists equal as multisets are equal as lists.

## 2. The algorithm

**Randomness model.** A run of the algorithm on input $L$ is a random
process: at each recursive call on a sublist of length $m > 0$ it
draws an index $I$ uniformly from $\{0, \dots, m-1\}$, independently
of all other draws. The sample space $\Omega_L$ is the (finite) set of
all sequences of such draws, equipped with the product of the uniform
measures; the output is a random variable
$\mathrm{QS}(L) : \Omega_L \to \alpha^{n}$.

**Algorithm** $\mathrm{QS}(L)$:

1. If $L = ()$, return $()$.
2. Otherwise draw $I \sim \mathrm{Unif}\{0, \dots, |L|-1\}$ and let
   $p := a_I$ (the *pivot*); let $R$ be $L$ with position $I$ removed.
3. Partition $R$ into
   $L_{<} := (x \in R : x < p)$ and $L_{\ge} := (x \in R : x \ge p)$,
   preserving order of appearance ($|R| = |L|-1$ comparisons).
4. Recursively compute $S_1 := \mathrm{QS}(L_{<})$ and
   $S_2 := \mathrm{QS}(L_{\ge})$, and return $S_1 \mathbin{+\!\!+} (p) \mathbin{+\!\!+} S_2$.

**Cost model.** One unit of cost per comparison against the pivot:
a call at length $m > 0$ costs exactly $m - 1$, base calls cost $0$.
The total cost of a run is the sum over all recursive calls; it is a
random variable $C(L) : \Omega_L \to \mathbb{N}$.

## 3. Correctness

**Theorem 1 (correctness).** For every list $L$,
$$\Pr[\mathrm{QS}(L) = \mathrm{sort}(L)] = 1 .$$
That is, the output distribution is the Dirac measure
$\delta_{\mathrm{sort}(L)}$: the algorithm is Las Vegas — the
randomness affects only its running time, never its answer.

*Proof.* By strong induction on $|L|$. For $L = ()$ the algorithm
returns $()$ = $\mathrm{sort}(())$ deterministically. For $|L| \ge 1$,
condition on the pivot index $I = i$; it suffices to show every branch
returns $\mathrm{sort}(L)$ with probability $1$. Write $p = a_i$, and
let $L_<, L_\ge$ be the partition of $R$ (step 3). Both have length
$< |L|$, so by the induction hypothesis the recursive calls return
$\mathrm{sort}(L_<)$ and $\mathrm{sort}(L_\ge)$ almost surely. It
remains to check the deterministic identity
$$\mathrm{sort}(L_<) \mathbin{+\!\!+} (p) \mathbin{+\!\!+} \mathrm{sort}(L_\ge) = \mathrm{sort}(L),$$
which holds because (i) the concatenation is sorted — every element of
$L_<$ is $< p$ and every element of $L_\ge$ is $\ge p$; and (ii) as a
multiset it equals $L_< \uplus \{p\} \uplus L_\ge = L$; a sorted list
with the multiset of $L$ is $\mathrm{sort}(L)$. $\blacksquare$

## 4. Complexity

Write $H_n := \sum_{r=1}^{n} 1/r$ for the $n$-th harmonic number.

**Theorem 2 (exact expected cost, distinct elements).** If the entries
of $L$ are pairwise distinct and $|L| = n$, then
$$\mathbb{E}[C(L)] \;=\; 2(n+1)H_n - 4n .$$

*Proof.* Since only the relative order matters, assume
$L$ is a permutation of $\{1, \dots, n\}$ and identify each element
with its rank. For $1 \le i < j \le n$ let $X_{ij}$ be the indicator
of the event that elements $i$ and $j$ are ever compared. Two elements
are compared exactly when one of them is chosen as pivot in a call
whose sublist still contains both — and they are compared at most
once, so $C(L) = \sum_{i<j} X_{ij}$.

*Claim:* $\Pr[X_{ij} = 1] = \dfrac{2}{j-i+1}$. Consider the set
$B_{ij} = \{i, i+1, \dots, j\}$ of ranks between $i$ and $j$. As long
as no element of $B_{ij}$ has been chosen as pivot, all of $B_{ij}$
stays together in the same sublist (a pivot outside $B_{ij}$ sends the
whole block to one side). At the first call whose pivot lies in
$B_{ij}$, that pivot is uniform on $B_{ij}$ (uniform pivoting on a
sublist containing all of $B_{ij}$ induces the uniform distribution on
$B_{ij}$, conditioned on hitting it); the pair $(i,j)$ is compared iff
this first pivot is $i$ or $j$, which has probability $2/|B_{ij}| =
2/(j-i+1)$; afterwards $i$ and $j$ are separated and never compared.

By linearity of expectation,
$$\mathbb{E}[C(L)]
 = \sum_{1 \le i < j \le n} \frac{2}{j-i+1}
 = \sum_{d=1}^{n-1} (n-d)\,\frac{2}{d+1}
 = 2\sum_{d=1}^{n-1}\frac{n+1}{d+1} - 2\sum_{d=1}^{n-1}\frac{d+1}{d+1}
$$
$$
 = 2(n+1)(H_n - 1) - 2(n-1) \;=\; 2(n+1)H_n - 4n . \qquad\blacksquare$$

*(Sanity check: $n = 2$ gives $2\cdot 3\cdot\tfrac32 - 8 = 1$, one
comparison, as it must.)*

**Theorem 3 (quadratic bound, arbitrary lists).** For every list $L$
(duplicates allowed), $\mathbb{E}[C(L)] \le \binom{n}{2}$.

*Proof.* By strong induction on $n$. The call costs $n - 1$ and
recurses on $L_<$ and $L_\ge$ with $|L_<| + |L_\ge| = n - 1$. By the
induction hypothesis and monotonicity of $\binom{\cdot}{2}$,
$$\mathbb{E}[C(L)] \le (n-1) + \binom{|L_<|}{2} + \binom{|L_\ge|}{2}
  \le (n-1) + \binom{n-1}{2} = \binom{n}{2},$$
using $\binom{a}{2} + \binom{b}{2} \le \binom{a+b}{2}$ (a standard
convexity fact; proof omitted). $\blacksquare$

*Remark (tightness).* The bound is attained: when all entries are
equal, $L_< = ()$ and $L_\ge = R$ in every call, so the cost is
deterministically $(n-1) + (n-2) + \dots + 1 = \binom{n}{2}$.
(Observation only — the formalization proves the inequality.)

## 5. Auxiliary facts used (stated, not proved)

* Two sorted lists that are equal as multisets are equal as lists.
* $\sum_{d=1}^{n-1} \frac{1}{d+1} = H_n - 1$.
* $\binom{a}{2} + \binom{b}{2} \le \binom{a+b}{2}$ for all
  $a, b \in \mathbb{N}$.

*Note on Theorem 2.* The pair-indicator argument above is the classical
one. The formalization establishes the same constant
$2(n+1)H_n - 4n$ by the equivalent route: induction on the
uniform-pivot recurrence, closed by telescoping the harmonic sums.
