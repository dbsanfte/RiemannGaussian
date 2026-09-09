# Testing all divisor weights analytically

[SuzukiDivisorDualOptimality.lean](../RiemannGaussian/SuzukiDivisorDualOptimality.lean)
answers the question whether weight families must be tested one at a time.
It identifies the exact optimum over all finite weights, characterizes every
optimizer, and provides a simultaneous upper bound for any specified weight
class. It does not establish a uniform arithmetic floor or a new zero bound.

The subsequent [complete quotient construction](suzuki-divisor-quotient-optimizer.md)
gives explicit finite Möbius coefficients attaining the optimum for every
endpoint and center. It removes approximation loss without proving the
remaining uniform arithmetic floor.

## The unrestricted optimum is known exactly

Use the notation of the
[corrected Legendre interface](suzuki-legendre-divisor-dual.md):
`f_r(d)=(log d-r)/sqrt d`, `K_w(d)=sum_{d|m, m<=N} w(m)`, and
`L_N(r)=sum_{d<=N} Lambda(d)*f_r(d)`.

Lean proves that every finite target kernel can be attained exactly:

\[
\forall f\ \exists w,\quad K_w(d)=f(d)\quad(1\le d\le N).
\]

This is `exists_suzukiDivisorDualKernel_eq`. The proof is finite descending
elimination. In elementary notation it amounts to starting at `N` and using

\[
w(d)=f(d)-\sum_{2\le k\le N/d}w(dk).
\]

No numerical search, Möbius cancellation estimate, or zero hypothesis is
needed. Combined with the signed slack identity, it proves

\[
\boxed{\max_{w:K_w\le f_r}\sum_{m\le N}w(m)\log m=L_N(r).}
\]

`suzukiLegendreLinearForm_isGreatest_dual` proves both attainment and the
universal upper bound. At the exact mass center the literal Suzuki result is

\[
\boxed{\max_{w\text{ feasible}}\operatorname{certificate}_N(w)=B_N.}
\]

This is `suzukiMassLegendrePotential_isGreatest_dual`. Thus the finite
optimization problem is completely solved at the level of its value.
The still-missing theorem is a lower bound on that value uniform in `N`.
Allowing every weight family does not bypass the original arithmetic floor.

## Every optimizer is characterized by its prime-power contacts

For feasible weights the exact loss is

\[
L_N(r)-\sum_{m\le N}w(m)\log m
=\sum_{d\le N}\Lambda(d)\bigl(f_r(d)-K_w(d)\bigr).
\]

Every summand is nonnegative, and `Lambda(d)>0` exactly at prime powers.
`suzukiLegendreLinearForm_eq_dual_iff` therefore proves

\[
w\text{ is optimal}\quad\Longleftrightarrow\quad
K_w(p^k)=f_r(p^k)\text{ for every }p^k\le N.
\]

Here `p` is prime and `k>=1`. Kernel slack at all other integers contributes
zero to the objective. Exact equality at every integer is a sufficient
construction, but it is not required for optimality. The theorem does not
assert a unique weight vector. It preserves the exact arithmetic support
that a norm or a uniform unweighted error estimate would obscure.

There is also a stronger certificate interface:
`suzukiLegendreLinearForm_ge_dual_on_primePowers` and
`suzukiMassLegendrePotential_ge_of_primePower_divisorDual` require the
minorant inequality **only at prime powers**. All other constraints can be
removed, since their von Mangoldt mass is zero. The preceding numerical
screens enforced them and therefore searched a more restrictive feasible set.
The original maximum remains an upper bound for the enlarged set and is
already attained by the exact-kernel construction.

## A test for a whole class at once

Choose finitely many basis weights `phi_j`, allowing arbitrary real
coefficients in `w=sum_j a_j*phi_j`. Suppose one nonnegative comparison mass
`nu(d)` reproduces the basis observations:

\[
\sum_{d\le N}\nu(d)K_{\phi_j}(d)
=\sum_{m\le N}\phi_j(m)\log m\qquad\text{for every }j.
\]

Then every feasible coefficient choice simultaneously satisfies

\[
\boxed{\sum_{m\le N}w(m)\log m
\le\sum_{d\le N}\nu(d)f_r(d).}
\]

`suzukiDivisorDual_span_upper_bound` proves this from the finite basis
equalities alone, including signed coefficients. The companion
`suzukiDivisorDual_class_upper_bound` works for an arbitrary set of weights
whose observations are matched. The comparison mass need not be von Mangoldt.

These two class theorems use the original all-integer minorant test. When
applying the prime-power-only relaxation, a comparison mass must also
vanish outside prime powers, or else its extra positive masses would rely
on inequalities the relaxed certificate no longer requires. A bad
all-integer comparison alone does not rule out the enlarged class.

This is an application of weak linear-programming duality, proved directly
with finite sums here; see also
[Boyd and Vandenberghe's duality slides](https://web.stanford.edu/~boyd/cvxbook/bv_cvxslides.pdf#page=165).
No general strong-duality theorem is used or newly formalized.

Adding the common Archimedean terms gives a ceiling on every certificate in
the class. If an explicit sequence of such comparison masses has ceilings
below every finite floor at arbitrarily large endpoints, the entire class
is ruled out, irrespective of how its coefficients are tuned. This would
turn a numerical failure pattern into one analytic obstruction theorem.
That divergent comparison family has not yet been constructed.

A comparison mass giving a large ceiling does **not** prove that the class
can achieve a good lower certificate. Success still requires a feasible
certificate with a proved floor, or a justified lower bound on the optimum.
The proposed next use is to identify which divisor observations admit bad
comparison masses, then preserve additional information that excludes them.

## Scope and verification

The eight public theorems are exact finite results. They replace individual
weight guessing with an optimizer characterization and a class comparison
test. They do not prove that the numerical smooth-weight families fail
asymptotically, or that some other family yields a bounded floor.

Direct warnings-as-errors, focused/full builds, whole-project declaration
lint, and a root-import verbose lint and explicit axiom audit verify the
module. All eight terminal theorems use only `propext`, `Classical.choice`,
and `Quot.sound`. The RH goal and generated `rhImplied:false` remain unchanged.
