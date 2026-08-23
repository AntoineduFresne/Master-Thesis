# The Coupon Collector

## 1. Problem

There are $n$ distinct coupon types. Each draw yields a coupon type
chosen uniformly at random, independently of all other draws. How
many draws are needed, in expectation, until every type has been
seen at least once? The classical answer:
$$\mathbb{E}[\text{draws}] \;=\; n \, H_n
 \;=\; n \sum_{r=1}^{n} \frac{1}{r} \;=\; n \ln n + O(n).$$

## 2. The process and its cost law

**Stage decomposition.** Order the process into stages: stage $m$
(for $m = n, n-1, \dots, 1$) begins when $n - m$ distinct types have
been seen and ends when a new type appears. During stage $m$, each
draw is new with probability $p_m = m/n$, independently across draws.

**Geometric stages.** The number of draws in stage $m$ is therefore
distributed as a geometric random variable: with $q_m := 1 - p_m$,
$$\Pr[\text{stage } m \text{ takes } k + 1 \text{ draws}]
 = q_m^{\,k}\, p_m \qquad (k = 0, 1, 2, \dots),$$
and the stages are independent. The total number of draws is
$T_n := \sum_{m=1}^{n} G_m$ where $G_m$ is the number of draws of
stage $m$ (support $\{1, 2, \dots\}$).

**Remark (modelling).** "Draw until new" is a retry loop that
terminates only almost surely — there is no deterministic bound on
its length, so it cannot be written as a structurally terminating
program. Its cost law is nevertheless a perfectly well-defined
probability distribution on $\mathbb{N}$ (the geometric law has total
mass $\sum_k q^k p = p \cdot \frac{1}{1-q} = 1$ for $p > 0$), and the
process above defines the distribution of $T_n$ as the law of a sum
of independent geometrics. We analyze that law directly; the
program-level retry loop is exactly the Las-Vegas construct that
needs sub-probability semantics.

## 3. Expectation of a geometric law

**Lemma 1.** Let $0 \le q < 1$ and let $G$ take value $k$ with
probability $q^k(1-q)$ for $k \in \mathbb{N}$ (failures before the
first success). Then
$$\mathbb{E}[G] = \sum_{k \ge 0} k\, q^k (1-q) = \frac{q}{1-q}.$$

Proof. Write $k = \#\{j : j < k\}$ and exchange the two sums
(all terms are nonnegative, so the exchange is unconditional):
$$\sum_{k} k\, q^k (1-q)
 = \sum_{k}\sum_{j < k} q^k (1-q)
 = \sum_{j}\sum_{k \ge j+1} q^k (1-q)
 = \sum_{j} q^{\,j+1} \frac{1-q}{1-q}
 = \sum_{j} q^{\,j+1} = \frac{q}{1-q},$$
using the geometric series $\sum_{k \ge j+1} q^k = q^{\,j+1}/(1-q)$
twice. $\blacksquare$

**Corollary.** The number of draws of a stage with success
probability $p > 0$ is $G + 1$, with
$\mathbb{E}[G + 1] = \frac{1-p}{p} + 1 = \frac{1}{p}$.

## 4. The theorem

**Theorem (coupon collector).** For every $n$,
$$\mathbb{E}[T_n] \;=\; \sum_{m=1}^{n} \frac{1}{p_m}
 \;=\; \sum_{m=1}^{n} \frac{n}{m} \;=\; n\,H_n .$$

Proof. By linearity of expectation over the (independent) stages
and the corollary: stage $m$ has success probability $p_m = m/n > 0$,
so it contributes $1/p_m = n/m$ expected draws; summing over
$m = 1, \dots, n$ gives $n H_n$. (Linearity does not need
independence; the stage decomposition is by construction of the
law.) $\blacksquare$

Sanity check ($n = 2$): the first draw is always new, the second
type is a fair coin per draw: $1 + 2 = 3 = 2 \cdot H_2 = 2 \cdot
\tfrac32$. ✓

## 5. Auxiliary facts used (stated, not proved)

* Geometric series: $\sum_{k \ge 0} q^k = (1-q)^{-1}$ for
  $0 \le q < 1$, and its tail form
  $\sum_{k \ge j+1} q^k = q^{j+1}(1-q)^{-1}$.
* Tonelli for nonnegative double series (sum exchange).
* $H_n = \sum_{r=1}^n 1/r$.
