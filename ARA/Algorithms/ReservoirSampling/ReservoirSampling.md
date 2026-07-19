# Reservoir Sampling (Algorithm R, $k = 1$)

## 1. Problem

Given a finite list $L = (a_0, \dots, a_{n-1})$ presented as a
stream — one element at a time, length unknown in advance — output a
uniformly random element of $L$ using $O(1)$ memory: for every value
$a$,
$$\Pr[\text{output} = a] \;=\; \frac{\#\{i : a_i = a\}}{n},$$
i.e. the output law is the empirical distribution of the list (for
distinct entries, uniform: each entry with probability $1/n$). On the
empty list a designated symbol $\bot$ is returned.

## 2. The algorithm

**Randomness model.** While processing the $i$-th stream element
($i \ge 2$, one-indexed), the algorithm draws an independent uniform
variable $U_i \sim \mathrm{Unif}\{0, 1, \dots, i-1\}$; the sample
space is the product of these finitely many uniform draws.

**Algorithm** $\mathrm{Res}(L)$:

1. If the stream is empty, return $\bot$.
2. Hold the first element: $\mathrm{cur} := a_0$, $\mathrm{seen} := 1$.
3. For each subsequent element $x$: draw
   $U \sim \mathrm{Unif}\{0, \dots, \mathrm{seen}\}$; if $U = 0$
   replace $\mathrm{cur} := x$ (probability
   $\tfrac{1}{\mathrm{seen}+1}$), otherwise keep $\mathrm{cur}$;
   increment $\mathrm{seen}$.
4. Return $\mathrm{cur}$.

**Cost model.** One unit per stream element processed after the
first (one coin draw each): the cost is deterministic.

## 3. Correctness (exact output distribution)

**Lemma (streaming invariant).** Suppose the loop is entered with
$\mathrm{seen} = s \ge 1$, held element $c$, and remaining stream
$x_1, \dots, x_r$. Then for every value $y$,
$$\Pr[\text{final } \mathrm{cur} = y]
 = \frac{s\,[y = c] + \#\{t : x_t = y\}}{s + r},$$
where $[\,\cdot\,]$ is the Iverson bracket: the held element carries
weight $s$, every remaining element carries weight $1$ (per
occurrence), normalized by the total $s + r$.

*Proof.* Induction on $r$. For $r = 0$ the claim reads
$\Pr[\mathrm{cur} = y] = [y = c]$, true deterministically. Step: the
next element $x_1$ is adopted with probability $\tfrac{1}{s+1}$ and
rejected with probability $\tfrac{s}{s+1}$; in both cases the loop
continues with $\mathrm{seen} = s + 1$ and remaining stream
$x_2, \dots, x_r$. By the induction hypothesis,
$$\Pr[\text{final} = y]
 = \frac{1}{s+1}\cdot\frac{(s+1)[y = x_1] + N'}{s+1+(r-1)}
 + \frac{s}{s+1}\cdot\frac{(s+1)[y = c] + N'}{s+1+(r-1)},$$
where $N' := \#\{t \ge 2 : x_t = y\}$. The numerators combine to
$(s+1)\bigl(s[y=c] + [y=x_1] + N'\bigr)$, the $(s+1)$ cancels, and
$[y = x_1] + N' = \#\{t : x_t = y\}$, giving the claim.
$\blacksquare$

**Theorem 1 (exact law).** For every nonempty $L$ and every $a$,
$$\Pr[\mathrm{Res}(L) = a] = \frac{\#\{i : a_i = a\}}{n},$$
and $\Pr[\mathrm{Res}(L) = \bot] = 0$. In particular, for pairwise
distinct entries, every member of $L$ is output with probability
exactly $1/n$.

*Proof.* Apply the invariant with $s = 1$, $c = a_0$, remaining
stream $a_1, \dots, a_{n-1}$: the weight of $a$ is
$[a = a_0] + \#\{i \ge 1 : a_i = a\} = \#\{i : a_i = a\}$ over the
total $1 + (n-1) = n$. The algorithm always holds some stream
element, so $\bot$ is never returned. $\blacksquare$

## 4. Complexity

**Theorem 2 (exact cost).** The algorithm makes exactly $n - 1$ coin
draws on a list of length $n \ge 1$ (and $0$ on the empty list): a
single pass, deterministically.

*Proof.* One draw per loop iteration, one iteration per element after
the first. $\blacksquare$
