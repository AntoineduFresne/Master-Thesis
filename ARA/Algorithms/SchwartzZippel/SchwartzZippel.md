# Schwartz–Zippel Polynomial Identity Testing

## 1. Problem

Let $R$ be a commutative ring that is an integral domain, and let
$P \in R[X_1, \dots, X_n]$ be a multivariate polynomial. Decide
whether $P$ is the zero polynomial — given only the ability to
*evaluate* $P$ at chosen points. Deterministically this can require
exponentially many evaluations; we allow a **Monte-Carlo** tester
with one-sided error: it must always accept the zero polynomial, and
accept a nonzero one with probability at most $d/|S|$, where $d$ is
the total degree of $P$ and $S$ a chosen finite evaluation set.

Polynomial identity testing ($P \stackrel{?}{=} Q$ via $P - Q
\stackrel{?}{=} 0$) is the canonical application; Freivalds'
matrix-product verification is the special case of the bilinear
polynomial $x^{\mathsf T}(AB - C)\,y$ tested on $\{0,1\}$-vectors.

## 2. The algorithm

**Randomness model.** Fix a finite nonempty $S \subseteq R$. The
algorithm draws one uniformly random point $r$ of the grid
$S^n$ — equivalently, $n$ independent coordinates
$r_1, \dots, r_n \sim \mathrm{Unif}(S)$; the sample space is $S^n$
with the uniform measure ($|S|^{-n}$ per point).

**Algorithm** $\mathrm{SZ}(P, S)$:

1. Draw $r \sim \mathrm{Unif}(S^n)$.
2. Accept (output "zero") iff $P(r) = 0$.

**Cost model.** The single polynomial evaluation is charged
wholesale: cost exactly $1$ oracle call, deterministically.

## 3. Correctness

**Theorem 1 (completeness).** If $P = 0$ the algorithm accepts with
probability $1$. *Proof.* $P(r) = 0$ for every $r$. $\blacksquare$

**Theorem 2 (Schwartz–Zippel; soundness).** If $P \ne 0$ has total
degree $d$, then
$$\Pr_{r \sim \mathrm{Unif}(S^n)}\bigl[P(r) = 0\bigr]
 \;=\; \frac{\#\{r \in S^n : P(r) = 0\}}{|S|^n}
 \;\le\; \frac{d}{|S|} .$$

*Proof.* By induction on the number of variables $n$.

*Base $n = 0$:* a nonzero constant never evaluates to $0$; the
left-hand side is $0$.

*Step:* write $P$ as a polynomial in $X_n$ with coefficients in
$R[X_1, \dots, X_{n-1}]$:
$$P = \sum_{i=0}^{k} P_i(X_1, \dots, X_{n-1})\, X_n^i,
 \qquad P_k \ne 0,$$
where $k$ is the degree of $P$ in $X_n$; then
$\deg P_k \le d - k$ (the monomials of $P_k X_n^k$ have total degree
$\le d$). Split the event $P(r) = 0$ by whether the leading
coefficient vanished:

* **Case A: $P_k(r_1, \dots, r_{n-1}) = 0$.** By the induction
  hypothesis applied to $P_k \ne 0$ (in $n-1$ variables, total degree
  $\le d - k$), this happens with probability at most
  $(d-k)/|S|$.
* **Case B: $P_k(r_1, \dots, r_{n-1}) \ne 0$.** Condition on the
  values $r_1, \dots, r_{n-1}$; the univariate polynomial
  $p(X) := P(r_1, \dots, r_{n-1}, X) \in R[X]$ is nonzero of degree
  exactly $k$. Over an integral domain a nonzero univariate
  polynomial of degree $k$ has at most $k$ roots (stated below), so
  the independent uniform draw $r_n$ hits a root with probability at
  most $k/|S|$.

By the union bound,
$$\Pr[P(r) = 0] \;\le\; \frac{d-k}{|S|} + \frac{k}{|S|}
 \;=\; \frac{d}{|S|}. \qquad\blacksquare$$

**Remark (one-sided error and amplification).** The tester never
rejects the zero polynomial; $k$ independent runs, rejecting if any
run rejects, accept a nonzero polynomial with probability at most
$(d/|S|)^k$.

## 4. Complexity

**Theorem 3.** Every run costs exactly $1$ oracle evaluation — the
cost law is the point mass at $1$, not merely a mean. $\blacksquare$

## 5. Auxiliary facts used (stated, not proved)

* A nonzero univariate polynomial of degree $k$ over an integral
  domain has at most $k$ roots (factor theorem + induction).
* The counting bound of Theorem 2 itself: the induction above is the
  classical argument (Schwartz 1980, Zippel 1979), and the
  formalization consumes it as a library fact rather than replaying
  it, exactly as it does the root bound.
* The union bound.
* Conditioning: the coordinates of a uniform sample of $S^n$ are
  independent and uniform on $S$.
