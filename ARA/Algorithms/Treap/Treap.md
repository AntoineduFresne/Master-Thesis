# Treaps / Randomized Binary Search Trees

## 1. Problem

Store a finite set of keys $K \subseteq \mathbb{N}$, $|K| = n$, in a
**binary search tree** (BST) whose shape is randomized so that its
expected height is $O(\log n)$ — without rebalancing logic. A binary
tree is either a leaf or a node $(\ell, x, r)$ with subtrees $\ell,
r$ and key $x$; its inorder traversal lists left subtree, key,
right subtree; it is a BST over $K$ iff the inorder traversal is the
strictly increasing enumeration of $K$. The height $h(t)$ is
$0$ for a leaf and $1 + \max(h(\ell), h(r))$ for a node.

## 2. The two models

**Insertion model** $\mathrm{RBST}(K)$: draw a uniformly random
ordering of the keys (a uniform shuffle) and insert them, in that
order, into an initially empty BST with the standard (unbalanced)
insertion procedure.

**Recursive model** $\mathrm{Treap}(L)$, for a list $L$ of distinct
keys: if $L = ()$ return a leaf; otherwise draw a uniformly random
position $I$, make $p := L_I$ the root, and recurse independently on
$(x \in L \setminus_I : x < p)$ for the left subtree and
$(x \in L \setminus_I : x \ge p)$ for the right.

These are the two classical descriptions of the same object (the
treap: BST on keys, heap on i.i.d. priorities); the formal
equivalence of the two output distributions reduces, by the
exchangeability of the uniform shuffle, to the fact that a uniform
permutation's first element is a uniform key and the relative orders
of the two sides are again uniform. (The distributional equivalence
is stated here as the target of ongoing work; the theorems below are
proved per model.)

**Cost model.** No operational cost is charged; the quantity of
interest is structural — the height of the returned tree, a random
variable through the output distribution.

## 3. Correctness

**Theorem 1 (both models produce BSTs).** Let the keys be distinct.
Every tree $t$ in the support of $\mathrm{RBST}(K)$ (resp.
$\mathrm{Treap}(L)$) satisfies: the inorder traversal of $t$ is
strictly increasing and is a permutation of the keys. In particular
the traversal is deterministic even though the shape is random.

Proof (insertion model). By Theorem 1 of the Fisher–Yates
companion, the shuffled list is a permutation of the keys. Standard
BST insertion preserves the invariants "inorder is strictly
increasing" and "inorder is a permutation of the multiset of keys
inserted so far" (stated; routine structural induction on the tree).
Folding over the whole permutation yields the claim.

Proof (recursive model). Strong induction on $|L|$: the root $p$
separates the strictly smaller keys (left) from the larger ones
(right); by the induction hypothesis both subtrees are BSTs over
their key sets, and concatenating
$\text{inorder}(\ell), p, \text{inorder}(r)$ is strictly increasing
and enumerates all keys. $\blacksquare$

**Theorem 2 (deterministic height bound).** In both models, every
supported tree has height $\le n$: by Theorem 1 the traversal of such
a tree enumerates the $n$ keys, so the tree has exactly $n$ nodes, and
the height of a binary tree is at most its number of nodes.
$\blacksquare$

## 4. Expected height

For the recursive model, let $H_n := h(\mathrm{Treap}(L))$ for a
list of $n$ distinct keys (the law of the height depends only on
$n$).

**Theorem 3 (exponential-height bound).**
$$\mathbb{E}\bigl[2^{H_n}\bigr] \;\le\; \binom{n+3}{3}.$$

Proof. Induction on $n$; write $Y_n := 2^{H_n}$. For $n = 0$,
$Y_0 = 1 = \binom{3}{3}$. For $n \ge 1$, condition on the root's
rank $j \in \{0, \dots, n-1\}$ (uniform: the uniformly chosen root
is the $(j{+}1)$-st smallest key with probability $1/n$); the two
subtrees are independent recursive treaps on $j$ and $n-1-j$ keys,
and $2^{h} = 2\max(2^{h(\ell)}, 2^{h(r)}) \le 2(Y_j' + Y_{n-1-j}'')$,
so
$$\mathbb{E}[Y_n] \le \frac{2}{n}\sum_{j=0}^{n-1}
 \Bigl(\mathbb{E}[Y_j] + \mathbb{E}[Y_{n-1-j}]\Bigr)
 = \frac{4}{n}\sum_{j=0}^{n-1}\mathbb{E}[Y_j]
 \le \frac{4}{n}\sum_{j=0}^{n-1}\binom{j+3}{3}
 = \frac{4}{n}\binom{n+3}{4},$$
by the hockey-stick identity
$\sum_{j=0}^{n-1}\binom{j+3}{3} = \binom{n+3}{4}$; and
$4\binom{n+3}{4} = n\binom{n+3}{3}$, closing the induction with
equality in the last step. $\blacksquare$

**Theorem 4 (logarithmic expected height).**
$$\mathbb{E}[H_n] \;\le\; 3\lfloor\log_2(n+3)\rfloor + 4 .$$

Proof. For every $k \in \mathbb{N}$ and every $h \in \mathbb{N}$,
$$h \le k + \frac{2^h}{2^k}$$
(if $h \le k$ this is clear; if $h > k$ then $2^{h-k} \ge h - k$).
Taking expectations and choosing
$k := \lfloor\log_2 \binom{n+3}{3}\rfloor + 1$, so that
$2^k > \binom{n+3}{3} \ge \mathbb{E}[2^{H_n}]$:
$$\mathbb{E}[H_n] \le k + \frac{\mathbb{E}[2^{H_n}]}{2^k}
 \le k + 1
 = \Bigl\lfloor\log_2 \binom{n+3}{3}\Bigr\rfloor + 2 .$$
Finally $\binom{n+3}{3} \le (n+3)^3$ gives
$\lfloor\log_2\binom{n+3}{3}\rfloor \le
 \lfloor 3\log_2 (n+3)\rfloor \le 3\lfloor\log_2(n+3)\rfloor + 2$,
hence $\mathbb{E}[H_n] \le 3\lfloor\log_2(n+3)\rfloor + 4$.
(No Jensen-type inequality is needed — only the pointwise bound
above. The sharp constant is $\approx 3$ in base $2$;
Devroye 1986.) $\blacksquare$

## 5. Auxiliary facts used (stated, not proved)

* BST insertion preserves sortedness and the key multiset of the
  inorder traversal.
* Hockey-stick identity:
  $\sum_{j=0}^{n-1}\binom{j+3}{3} = \binom{n+3}{4}$, and
  $4\binom{n+3}{4} = n\binom{n+3}{3}$.
* $2^{m} \ge m$ for $m \in \mathbb{N}$ (behind $h \le k + 2^h/2^k$).
* $\lfloor 3y \rfloor \le 3\lfloor y\rfloor + 2$.
