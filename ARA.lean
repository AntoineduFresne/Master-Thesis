import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-
  Framework for analysis of randomized algorithm.
  ARA = "Analysis of Randomized Algorithms"
  Author: Antoine du Fresne von Hohenesche
  Date: March 2026
-/

/-!
We use a shallow embedding setting "Giry Monad":

We utilize the `PMF` type (Probability Mass Function) which
for a type α is the type of function α → ℝ≥0∞ such that the
values have (infinite) sum 1.

Clearly any such function gives a probability measure on α on the set
of its parts (so singleton are measurable), by assigning
each set the sum of the probabilities of each of its elements.
This is done by the `toOuterMeasure` function:  PMF.toOuterMeasure.
PMF.toMeasure.isProbabilityMeasure shows this associated measure
is a probability measure.

Conversely any probability measure on α where singletons are measurable gives a PMF
by assigning to each element the measure of its singleton. This is done by the `toPMF`
function: .toPMF . These two functions are inverses of each other.

On top of this structure, Mathlib defines a monad structure on PMF (the Giry Monad),
with the following operations:

- `pure : α → PMF α` which takes a value and returns the distribution that is
  concentrated on that value (the Dirac distribution) i.e. assigns 1 to that
  value and 0 to all other values.

- `bind : PMF α → (α → PMF β) → PMF β` which for two types α and β:
  Takes (P,f) where :
  * P is a distribution over α, P : PMF α,
  * f is a function that assigns to each elements of α a distribution over β, f : α → PMF β
  Returns:
  the distribution over β obtained by "sampling" from the first distribution and
  then "sampling" from the second distribution. That is the probability of obtaining
  b in β from P.bind f is the sum over all a in α of the probability of a from P
  times the probability of obtaining b from f a, i.e. assigns b : β to the probability:
  ∑ a : α, P a * (f a) b

  It used concretely like this : pure x for pure x and P >>= f (or P.bind f) for bind (P,f).

The main advantage of having probability distributions in the logic is its
expressiveness and flexibility and also it is even possible to prove
that two algorithms with completely diﬀerent structure have not just the same
expected running time, but exactly the same distribution probability of outputs/running times.
-/
