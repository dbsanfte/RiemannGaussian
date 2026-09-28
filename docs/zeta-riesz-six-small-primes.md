# Joint signed bounds for the remaining six-small-prime sector

Both whole-sum estimates now use a sharper arithmetic bound on the six-prime
labels with no reflected-large prime. In this sector, the coefficient interval
improves from `[-3,4]` to `[-1,4]` in actual least-prime units. The existing
growing saddle-band credit and all prior reflection savings remain available.
The final independent whole floor `-79/1000-o(1)` and ceiling `3/2+o(1)` are
still open.

## The signed cancellation

Let `n` be squarefree with six prime factors. Write

\[
T=\log n,\qquad D=T-L,\qquad r=\log(\min p).
\]

Assume every prime logarithm is at most `D` and `3D <= T`. Lean proves

\[
\mathcal R_D(n)\le r.
\]

This is the complete Möbius divisor sum. The proof keeps the pair and triple
hinges together: after the higher subset hinges vanish, their signed sum has
one common least-logarithm budget. A finite case split covers every ordered
real six-logarithm configuration; each leaf is proved by real linear
arithmetic in Lean. Numerical optimization helped find the inequality and
case order, but no floating result or external solver certificate is trusted.

The older window-by-window argument gives `R_D <= 3r`. Bounding each window
by `r` would be false: the optional probe contains a window with signed value
three. The new result estimates the full finite difference before separating
its signs.

Even-count reflection and the original coefficient convention give

\[
-U_n\le\operatorname{Re}c_L(n)\le4U_n,
\qquad U_n=\frac{\log n}{L}\log(\min p).
\]

The upper coefficient bound `4U_n` is unchanged. No prime logarithm is
replaced by its mean. Equality at the cutoff is allowed in the coefficient
theorem; the whole-sum application selects precisely the sector with no
reflected-large prime and keeps the existing estimates elsewhere.

## Direct use in both whole estimates

Put `c=cos(y log n)`, `c_+=max(c,0)` and `c_-=max(-c,0)`. The two costs are

\[
\mathrm{floorCost}=U_n(c_++4c_-),\qquad
\mathrm{ceilingCost}=U_n(4c_++c_-).
\]

Compared with the previous `[-3,4]` interval, these save exactly `2U_n c_+`
in the floor and `2U_n c_-` in the ceiling. The literal residual weight
`weight A N n`, including the original unassigned factorial allocation and
kernel magnitude, multiplies these costs. Favorable observations remain:

\[
\max(\operatorname{Re}f_N(n),0)-w_N(n)\mathrm{floorCost}
\le\operatorname{Re}f_N(n)
\le\min(\operatorname{Re}f_N(n),0)+w_N(n)\mathrm{ceilingCost}.
\]

`eventually_core_subset_bounds` proves both inequalities on every exact
unpaid subset of the original core. The moving length supplies `3D <= T`
eventually for `1/2 < u <= 10001/20000`. The result is uniform in height,
count cutoff and choice of subset once that length condition holds. It uses
no zero, simplicity, prime-density or phase approximation premise.

The compiled optional application `CheckRieszSixSmallWhole` spends these
costs in **both** growing-band whole bounds on exactly

`S \ (union_i E_i union D_owner)`.

Every previous period credit, favorable observation and the single global
owner payment stays unchanged. The net credit is still at least
`(N/16)*sourceCredit`. The old twice-reflected estimates apply to labels with
one or more reflected-large primes; the new costs cover the remaining
six-prime labels. No population is paid twice. All other counts retain their
original signed atoms.

## Scope and checked sources

This reduces an independent adverse allowance; it does not prove the total
remaining allowance bounded at source scale. The other prime-count sectors,
unpaid share regions and radial complement still require a joint signed
estimate. No zero exclusion or RH contradiction follows.

- [Finite signed hinge inequality](../RiemannGaussian/ZetaRieszSixSmallHinges.lean)
- [Literal coefficients and both signed subset bounds](../RiemannGaussian/ZetaRieszSixSmallPrimes.lean)
- [Both complete whole-sum applications](../scripts/CheckRieszSixSmallWhole.lean)
- [Optional numerical exploration](../scripts/probe_riesz_six_small.py)
- [Verification and cached-cover audit](riesz-central-capacity-audit.json)

The whole applications reuse the existing checked cover cache. Exhaustive
numerical cover verification remains outside ordinary builds and CI.
