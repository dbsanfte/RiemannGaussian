# Quadratic profile correction and the common signed moment

The original `-79/1000` floor remains **open**. This is a quantitative audit
of a possible shortcut, not a new floor bound. A smaller logarithmic profile
energy need not give a smaller whole signed cost.

Proof: [ZetaRieszNullProfileAudit.lean](../RiemannGaussian/ZetaRieszNullProfileAudit.lean).
Validation: [proof and numerical audit](riesz-null-profile-audit.json).
Optional probe: [probe_riesz_profile_nulls.py](../scripts/probe_riesz_profile_nulls.py).

## Exact invariance does not pay the new coherent channel

Every original squarefree count-three label annihilates constants,
`log d` and `(log d)^2` in its divisor response. The existing
`corrected_prefix_eq` therefore permits arbitrary linear and quadratic
corrections. The literal atom, phases, allocation and masks are unchanged.

The original profile uses linear coefficient one and quadratic coefficient
zero. It is **exactly flat below the moving Riesz length**. Thus it avoids
charging the coherent low-cutoff channel at all.

`flat_early_iff` proves that, if `X>=3` and `L>=log 3`, keeping even the
first two increments flat forces those same coefficients:

\[
f(1)=f(2)=f(3)
\quad\Longleftrightarrow\quad
\mathrm{linear}=1,\qquad\mathrm{quadratic}=0.
\]

There is no nontrivial quadratic profile correction preserving this early
geometry for free. This says nothing against a correction whose new signed
moment is independently controlled.

## A fixed correction has a quantitative necessary cost

For the concrete near-least-energy profile

\[
f_N=\operatorname{correctedProfile}
  \left(X,L,\frac43,-\frac1{3N}\right),
\]

Lean proves exactly, for `X>=2`, `L>=log 2`,

\[
f_N(1)-f_N(2)
=-\left(\frac13-\frac{\log2}{3N}\right)\log2
\le-\frac{\log2}{4}\qquad(N\ge4).
\]

At cutoff one every actual integer has sharp prefix one. With the **entire
original signed weight sum** `M=sum_S w(n)`, the same existing comparison
cost must therefore satisfy

\[
\operatorname{negativeCost}(f_N)
\ge\frac{\log2}{4}\max(M,0),
\qquad
\operatorname{phaseEnergy}(f_N)\ge M^2.
\]

`native_candidate_common_lower` specializes the first inequality to the
actual `coreBand` and its exact source-normalized original phase/allocation
weight at `N>=65536`, without a zeta-zero hypothesis. The original support
can use any count ceiling. The nonempty-support condition only supplies
`X>=2`; no cancellation or arithmetic bound is assumed.

This is a **lower bound for the sufficient comparison cost**. It is not a
lower bound for the floor deficit, not a proof that the common moment grows,
and not a disproof of the arithmetic floor. Its actual size is unestimated.

## Quantitative probe before a larger development

The optional experiment reuses actual constructed probable-prime subsets
at native orders `256,640`, with original moving length, masks, allocation
and full phase. For each tested profile its adverse set is selected once
from the **entire subset**; all prefix columns/counts are joined first.
There is no binwise or countwise clipping.

The continuous least-energy coefficients on `[0,T]` are

\[
\lambda=L/T,\qquad
a=4\lambda-3\lambda^2,\qquad
b=3\lambda(\lambda-1)/T.
\]

Its total log-interpolated profile energy is

\[
T\lambda(1-\lambda)\bigl(1-3\lambda(1-\lambda)\bigr).
\]

The probe checks that formula and the exact divisor-response invariance
numerically. It also tests the **fixed** `4/3,-1/(3N)` coefficients appearing
in the Lean theorem, and fits the joined one-sided atomic cost numerically
with two optimizer starts. Optimizer output is not an optimality certificate.

Across twelve cases, using 24 and 48 labels, two seeds, and heights
`54,65,100`:

- The continuous least-energy correction reduces the profile price factor
  by roughly **77–78%**.
- Nevertheless its whole adverse Cauchy price **increases in eleven cases**.
  Ratios range from about `0.976` to `10.90`.
- The fixed Lean candidate likewise increases that price in eleven cases,
  with ratios from about `0.976` to `11.25`.
- Fitting the joined atomic cost gives at most about **5.98%** reduction in
  these tests; nine cases yield the same cost as the old flat profile.

These are floating diagnostics using continuous interpolation in `log k`,
not exact integer-energy or interval certificates. Common amplitude
rescaling is retained for underflow. They are tiny **constructed subsets**,
not full core populations or density samples; counts are only three through
ten, not the growing-count/many-bin frontier. They do not meet the eventual
Lean order threshold and cannot be compared with the native floor budget.
No asymptotic impossibility is inferred from them.

## Decision

Do not spend another slice reducing this profile factor alone. The new
low-cutoff moment has to be controlled jointly first; otherwise the apparent
profile saving can be consumed by the newly active signed energy. The
original flat profile remains available and unchanged. The native whole
signed energy budget, floor, ceiling and zero exclusion are unproved.

Nine public proofs pass focused Lean/root/lint/standard-axiom checks.
Earlier proofs, published README/explorer endpoints and staged semiprime
files remain unchanged. The probe is optional and outside builds/CI.
Work remains local, without commits, pushes or subagents.
