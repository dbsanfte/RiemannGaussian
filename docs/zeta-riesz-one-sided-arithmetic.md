# An independent one-sided arithmetic estimate

**Quantitative audit:** the proposed coarser allowance
`B_j - (3/4) B_4,j` is now proved to tend to **positive infinity** for
every fixed height and every `1/2 < u <= exp(-11/16)`. It cannot meet a
`3/40` ceiling on any cofinal subsequence. The finite lower bound below
remains valid, but this allowance cannot close the contradiction.
See the [proved complement obstruction](zeta-riesz-allowance-obstruction.md).

The actual remaining source-normalized carrier now has a proved lower
bound, independent of hypothetical zeros, exposure and simplicity:

$$
\operatorname{Re}R_j^{\rm nd}(u,y)
\ge -E_j(u,y)
\ge -B_j(u,y)+\frac34 B_{4,j}(u,y),\qquad u\ge0.
$$

Here `E_j = budget` is an explicit nonnegative one-sided arithmetic sum.
`B_j = antichainBudget` is the preceding absolute antichain allowance,
retaining the actual product cosine. `B_4,j = fourCharge` is its nonnegative
charge on the four-prime class specified below. These are finite sums on
the **actual** `nondominantBand`, with every previous mask, allocation
fraction, factorial envelope and physical cutoff intact.

The terminal theorem is
[`nondominantRemainder_lower_with_four_credit`](../RiemannGaussian/ZetaRieszOneSidedArithmetic.lean).
The stronger phase-dependent version is `nondominantRemainder_lower`.
The lower bounds hold at every order and height. **Neither `E_j <= 3/40`
nor a cofinal bound of that strength is proved.** There is no new zero
exclusion from this slice.

## The arithmetic evaluation

Write `t = log n`, `k = omega(n)`, and let `D = t-L` be the reflected
cutoff. Suppose the actual squarefree integer has at least three prime
factors and

$$
D\ge0,\qquad D/2\le\log p\le D\quad\text{for every prime }p\mid n.
$$

Every composite divisor then has logarithm at least `D`. Only the unit
and single primes contribute to the reflected Riesz sum. Lean evaluates it:

$$
\mathcal R_D(n)=t-(k-1)D,
\qquad
c_L(n)=-\frac{t}{L}(-1)^k\bigl((k-1)L-(k-2)t\bigr).
$$

This removes the Möbius divisor sum entirely from that class. The proof
retains its exact parity and radial sign. On the actual remaining support,
with `u >= 1/2` and `N >= 2`, Lean also proves **3 <= k <= 9** for this
class. It is an arithmetic subfamily of the remaining carrier, not a
claim that all remaining labels have at most nine prime factors.

## The quantitative four-prime saving

For four primes the literal coefficient is

$$
c_L(n)=\frac{t}{L}(2t-3L).
$$

Its sign changes at `t=3L/2`. Below that point nonpositive cosines have
zero lower-bound cost; above it nonnegative cosines have zero cost.
The actual atom's unassigned factor `1-theta_N(n)` stays nonnegative.

On the additional explicit radial window

$$
\frac{24}{17}L\le t\le\frac85L,
$$

Lean proves, for **every** phase,

$$
\max\{0,-c_L(n)\cos(yt)\}
\le \frac14\,\frac{t^2}{2L}\,|\cos(yt)|.
$$

The quantity `t^2/(2L)` is exactly the preceding four-prime antichain
allowance. Thus at least **75% of that subfamily's former charge** is
removed. This is not a 75% saving for the entire carrier. Summing the
proved pointwise inequality gives the displayed lower bound for the full
carrier, including every complementary prime count.

Outside the evaluated class, `E_j` keeps the existing antichain allowance.
Inside it, only the negative part of the explicit coefficient times the
original cosine is charged. `phaseCost_le_antichain` proves that this
change never enlarges the old budget. An upper bound on the coarser
`B_j - (3/4) B_4,j` is now ruled out. Further divisor evaluations can
strengthen `E_j` but cannot change that fixed target. A sufficient joint
signed estimate remains open; cancellation between labels must stay
available.

Sources: [exact reflected evaluation](../RiemannGaussian/ZetaRieszReflectedLinear.lean)
and [one-sided arithmetic bound](../RiemannGaussian/ZetaRieszOneSidedArithmetic.lean).
The [one-sided arithmetic explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=one-sided-arithmetic)
shows this finite estimate beside the separate obstruction to bounding its
fixed positive allowance.
