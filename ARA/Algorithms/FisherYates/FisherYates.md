# Fisher–Yates Shuffle

## 1. Problem

Given a finite list $L = (a_0, \dots, a_{n-1})$, output a
**uniformly random permutation** of $L$: when the entries are
pairwise distinct, every one of the $n!$ orderings of $L$ must occur
with probability exactly $1/n!$; for arbitrary lists, every output
must at least be a rearrangement of the input.

## 2. The algorithm

**Randomness model.** Each recursive call on a remaining list of
length $m > 0$ draws an index uniformly from $\{0, \dots, m-1\}$,
independently of all other draws; the sample space is the product of
these uniform draws, of size $n \cdot (n-1) \cdots 1 = n!$.

**Algorithm** $\mathrm{Shuffle}(L)$ (selection form):

1. If $L = ()$, return $()$.
2. Otherwise draw $I \sim \mathrm{Unif}\{0, \dots, |L|-1\}$, remove
   the entry at position $I$ — call it $h$ — and return
   $h$ followed by $\mathrm{Shuffle}(L \setminus_{\!I})$, where
   $L \setminus_{\!I}$ denotes $L$ with position $I$ deleted.

**Cost model.** The shuffle is a sampler: it consumes randomness
but is charged no cost (its clients pay for what they do with the
permutation).

## 3. Support: outputs are rearrangements

**Theorem 1.** For every list $L$ (duplicates allowed), every output
of $\mathrm{Shuffle}(L)$ is a permutation of $L$ (equal as
multisets) almost surely.

Proof. Strong induction on $|L|$. Empty case trivial. Otherwise
every output has the form $h :: t$ where $h$ is the entry removed at
position $I$ and, by the induction hypothesis, $t$ is a permutation
of $L \setminus_{\!I}$. Since $L$ is a permutation of
$h :: (L \setminus_{\!I})$ — deleting a position and re-consing the
deleted entry rearranges $L$ — transitivity gives the claim.
$\blacksquare$

## 4. Exact distribution

**Theorem 2 (pointwise uniformity / exchangeability).** Let the
entries of $L$ be pairwise distinct, $|L| = n$. Then for every
list $\pi$ that is a permutation of $L$,
$$\Pr[\mathrm{Shuffle}(L) = \pi] = \frac{1}{n!}.$$

Proof. Strong induction on $n$. For $n = 0$: the only permutation
of $()$ is $()$, returned with probability $1 = 1/0!$.

For $n \ge 1$ write $\pi = h :: t$. Conditioning on the first draw
$I$ (uniform on $n$ positions),
$$\Pr[\mathrm{Shuffle}(L) = h :: t]
 = \frac{1}{n} \sum_{i=0}^{n-1}
   \bigl[\,a_i = h\,\bigr]\cdot
   \Pr\bigl[\mathrm{Shuffle}(L \setminus_{\!i}) = t\bigr],$$
because a branch that puts $a_i \ne h$ first cannot produce
$h :: t$, and a branch with $a_i = h$ produces it exactly when the
recursive shuffle produces $t$.

Since the entries are distinct, exactly one index $i_0$ satisfies
$a_{i_0} = h$ (at least one because $h$ occurs in $\pi$, hence in
$L$; at most one by distinctness). Moreover $t$ is a permutation of
$L \setminus_{\!i_0}$ (cancel the common head $h$ from
"$h :: t$ is a permutation of $h :: (L\setminus_{\!i_0})$"), and
$L \setminus_{\!i_0}$ has $n - 1$ distinct entries; the induction
hypothesis gives
$\Pr[\mathrm{Shuffle}(L \setminus_{\!i_0}) = t] = 1/(n-1)!$. Hence
$$\Pr[\mathrm{Shuffle}(L) = \pi]
 = \frac{1}{n} \cdot \frac{1}{(n-1)!} = \frac{1}{n!}.
 \qquad\blacksquare$$

**Theorem 3 (the law is uniform).** For distinct entries, the output
distribution of $\mathrm{Shuffle}(L)$ is the uniform distribution
on the set of the $n!$ orderings of $L$.

Proof. By Theorem 2 the law assigns $1/n!$ to each of the $n!$
orderings; these probabilities sum to $1$, so (by Theorem 1, or by
mass alone) every other list has probability $0$. $\blacksquare$

**Remark (why this is exchangeability).** Theorem 2 is the
exchangeability lemma used to relate insertion-order models of
randomized data structures (e.g. treaps: "insert the keys in a
uniformly random order") to their recursive descriptions ("pick a
uniformly random root, recurse"): both reduce to the uniform measure
on permutations.

## 5. Complexity

**Theorem 4.** The shuffle is charged cost $0$: its cost law is the
point mass at $0$, so it is free on every run and not merely in
expectation — a pure sampler. $\blacksquare$

## 6. Auxiliary facts used (stated, not proved)

* Deleting position $i$ and prepending the deleted entry is a
  rearrangement: $L \sim a_i :: (L \setminus_{\!i})$.
* Left-cancellation of permutations: $h :: t \sim h :: t'$ implies
  $t \sim t'$.
* A list with $n$ distinct entries has exactly $n!$ orderings.
