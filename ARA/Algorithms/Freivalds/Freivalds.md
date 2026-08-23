# Freivalds' Matrix-Product Verification

## 1. Problem

Let $R$ be a commutative ring and $A, B, C \in R^{n \times n}$.
Decide whether $A B = C$ — faster than recomputing $AB$
($O(n^3)$ ring operations by the schoolbook method). We allow a
**Monte-Carlo** verifier with one-sided error: it must always accept
a true identity, and reject a false one with probability at least
$1/2$ per run.

## 2. The algorithm

**Randomness model.** The algorithm draws one uniform random vector
$r \in \{0,1\}^n \subseteq R^n$: the $n$ coordinates are independent
fair bits (here $0, 1 \in R$ are the ring's zero and one; no other
structure of $R$ is used). The sample space is $\{0,1\}^n$ with the
uniform measure ($2^{-n}$ per point).

**Algorithm** $\mathrm{Freivalds}(A, B, C)$:

1. Draw $r \sim \mathrm{Unif}(\{0,1\}^n)$.
2. Accept iff $A(Br) = Cr$, computing the three matrix–vector
   products $Br$, $A(Br)$, $Cr$.

**Cost model.** The three matrix–vector products are charged
wholesale: cost exactly $3n^2$, deterministically.

## 3. Correctness

Write $D := AB - C$; note $A(Br) = Cr \iff Dr = 0$, and $AB = C
\iff D = 0$.

**Theorem 1 (completeness).** If $AB = C$ the algorithm accepts with
probability $1$.

Proof. $D = 0$, so $Dr = 0$ for every $r$. $\blacksquare$

**Theorem 2 (soundness).** If $AB \ne C$ the algorithm accepts with
probability at most $1/2$ — over any commutative ring.

Proof. Since $D \ne 0$, fix indices $(i, j)$ with $D_{ij} \ne 0$.
Define the bit-flip involution
$\varphi : \{0,1\}^n \to \{0,1\}^n$ that flips the $j$-th
coordinate: $\varphi(r)_j = 1 - r_j$ and $\varphi(r)_l = r_l$ for
$l \ne j$. Then $\varphi \circ \varphi = \mathrm{id}$ and $\varphi$
is a bijection pairing the $2^n$ vectors into $2^{n-1}$ disjoint
pairs $\{r, \varphi(r)\}$.

Claim: at most one vector of each pair is accepting. The $i$-th
coordinate of $D\varphi(r)$ differs from that of $Dr$ by
$$\bigl(D\varphi(r)\bigr)_i - (Dr)_i \;=\; D_{ij}\,\varepsilon,
 \qquad \varepsilon = \pm 1 \in R,$$
because only the $j$-th coordinate of $r$ changed, by exactly
$\pm 1$. If both $r$ and $\varphi(r)$ were accepting, then
$(Dr)_i = 0 = (D\varphi(r))_i$, hence $D_{ij}\,\varepsilon = 0$; but
$\varepsilon$ is a unit ($\varepsilon^2 = 1$), so $D_{ij} = 0$ — a
contradiction. (Note: no zero divisors are needed; only that $\pm 1$
are units.)

Therefore the accepting set has at most one element per pair, i.e.
at most $2^{n-1}$ elements, and
$$\Pr[\text{accept}] = \frac{\#\{\text{accepting } r\}}{2^n}
 \le \frac{2^{n-1}}{2^n} = \frac{1}{2}. \qquad\blacksquare$$

**Remark (amplification).** $k$ independent runs, rejecting if any
run rejects, accept a false identity with probability at most
$2^{-k}$; completeness is preserved. This is the generic one-sided
Monte-Carlo amplification.

## 4. Complexity

**Theorem 3 (exact cost).** Every run costs exactly $3 n^2$:
sampling is free in the cost model and the three matrix–vector
products cost $n^2$ each — versus $n^3$ for recomputing $AB$.
$\blacksquare$

## 5. Auxiliary facts used (stated, not proved)

* A matrix–vector product over $R$ takes $n^2$ ring
  multiply–accumulate steps.
* An involution without fixed points partitions a finite set into
  two-element orbits.
