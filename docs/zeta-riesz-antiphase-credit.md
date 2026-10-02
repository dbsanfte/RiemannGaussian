# Signed credit across all original counts and phase periods

`ZetaRieszAntiphaseCredit` proves a signed inequality for the original
whole-floor energy. It fixes the adverse cutoff set using the entire
original core, then sums the divisor interaction across those cutoffs
before selecting any credit. All original counts, physical masks,
factorial allocation and total-label phase remain unchanged.

Write the original source-scaled weight as

\[
w_n=-a_n\cos(y\log n),\qquad a_n\ge0,
\]

and its joined divisor interaction as

\[
G(n,m)=\sum_{k\in K_{\mathrm{adverse}}}
\frac{\operatorname{sharp}(k,n)\operatorname{sharp}(k,m)}{k}.
\]

Within the previously unpaid pair population, retain pairs with
`G(n,m) >= 0` whose log difference is within

\[
\varepsilon_N=\frac{e^{-N/10000}}{1+|y|}
\]

of an odd half-period `(2k+1)*pi/y`. The finite period union covers every
possible such pair on the original finite label range; this is checked
by `antiphaseNear_of_resonance`. The joined Gram sign matters: opposite
phases alone do not give a favorable divisor interaction. No adverse
cutoff is reselected for these pairs.

The exact identity

\[
\cos\alpha\cos\beta
=-\frac{\cos^2\alpha+\cos^2\beta}{2}
+\frac{(\cos\alpha+\cos\beta)^2}{2}
\]

gives, for the entire original remaining energy,

\[
E_{\mathrm{direct}}=E_{\mathrm{rest}}-\mathcal R_N+\mathcal L_N.
\]

Here `reserve` is the literal nonnegative sum of
`a_n*a_m*G(n,m)*(cos(y*log n)^2+cos(y*log m)^2)/2`
over those retained ordered pairs. `leakage` is the same sum with the
squared cosine sum in place of the sum of squares. Both are nonnegative.
Neither `signedRest` nor `reserve` is replaced by a termwise norm.

Only the leakage is bounded absolutely. Cosine Lipschitz continuity gives
the square error `exp(-N/5000)`, while the reciprocal pair-capacity bound
supplies a further `exp(-N/10000)`. Including the actual squared source
growth and divisor Dirichlet exponent, Lean checks

\[
(2u)^{2(N+1)}e^{(3/262144-3/10000)N}
\le4U^2e^{-N/20000},\qquad U=10001/20000.
\]

Consequently

\[
0\le\mathcal L_N\le C_y(N+1)^4e^{-N/20000},
\]

where
`C_y=80*U^2*(phaseCount(y)+1)*M(1+1/262144)*exp(3/262144)`.
The convergent divisor mass is finite but unevaluated. This is a
fixed-height statement, not an effective numerical starting order.

The native joined-floor comparison is now

\[
\operatorname{Re}(u^{N+1}\operatorname{joinedPhysical})
\ge-\sqrt{\frac{129N}{200}
\max(E_{\mathrm{rest}}-\mathcal R_N,0)}-\mathrm{err}_N,
\qquad\mathrm{err}_N\to0.
\]

The added price is
`sqrt(4*C_y)*(N+1)^3*exp(-N/40000)`; the earlier diagonal, shared-factor,
near-label, aligned-phase and core/joined payments remain once.
There is no supply debit, clipped count credit, cropped original count
tail or hypothetical-zero assumption in this comparison.

This isolates a provable negative interaction across all counts and
periods and pays its imperfect matching geometrically. **It does not
prove a lower bound on the reserve's native size, or the needed small
upper bound on the signed rest minus the reserve.** That combined bound,
the numerical `-79/1000` floor, the ceiling and zero exclusion remain open.
The original direct energy already retained these signs; the new
inequality is not a monotonic numerical improvement over the exact
previous signed cost. It makes a negative credit available for bounding
the remainder without discarding it.

The next substantive task is to bound the actual
`signedRest-reserve` globally (a sufficient budget remains
`3/(320*(N+1))`), or the original signed floor directly. Do not spend a
slice merely tuning the leakage price or adding a conditional budget.
Opposite-phase occupancy and a nonnegative joined Gram on some pairs
are not an automatic lower bound on the reserve.

## Optional numerical diagnostic

`scripts/probe_riesz_antiphase_credit.py` is outside builds and CI. It
uses actual squarefree integer labels and divisor columns at orders 4/5,
with the exact rational moving length and full phase. Allocation is
empty at those orders. The original physical/annulus, dyadic and growing
count conditions are **not** certified. The native near-label strip
already covers every tested pair; the nonzero experiment instead uses
an explicitly diagnostic relative-distance threshold of `1/1000`.

All six cases at heights 54, 65 and 100 have positive credit. Five have a
smaller diagnostic price after keeping the credit than after dropping
it; the sixth worsens under the crude phase-leakage bound. All six
original remaining signed energies were already negative. These are
floating checks of the mechanism, not interval certificates or new
floor margins. No extrapolation to native/cofinal orders is justified.

Focused Lean/root/linter/standard-axiom validation is recorded in
`riesz-antiphase-credit-audit.json`. Earlier sources, staged semiprime
files and public explorer endpoints are preserved. Work remains local.

## Native-mask reflection and complete-cutoff diagnostic

`scripts/probe_riesz_reflected_phase_gram.py` constructs distinct probable
prime factors at the actual first two dyadic orders, `N=256,640` with
`K=8,16`. It checks the original core predicates numerically, including
the moving physical length, full allocation, nondominant owner and radial
window. It then joins all selected labels and divisor intervals before
examining interaction signs. It makes no prime-density approximation.

The existing exact squarefree reflection theorem explains the parity
information in the interaction:

\[
G(n,m)=\mu(n)\mu(m)\sum_{k\in K_{\mathrm{adverse}}}
\frac{\operatorname{sharp}((n-1)/k,n)
\operatorname{sharp}((m-1)/k,m)}{k}.
\]

Here the quotients are **integer quotients**. The reflected prefixes can
have either sign. The whole-label Möbius signs therefore do not determine
the sign of `G`. In particular, negative `G` and aligned cosines can give
favorable interactions; these are absent from the positive-`G` antiphase
reserve. The diagnostic also measures this second type without assuming
that it follows from opposite count parity.

Two runs, with 24 and 48 labels and heights 54, 65 and 100, give twelve
cases. Integer divisor reflection passes 273,312 interval/label checks,
and an independent direct Riesz sum agrees with the cutoff integral.
Both favorable interaction types occur. Their contributions vary greatly:
one negative-`G` aligned band captures about 99.89% of the favorable
cross-energy in its sample, while it is negligible in other samples.
Seven of the twelve remaining signed energies are positive; five are
negative. There is no uniform dominance in these samples.

The same probe joins the complete signed cutoff increments over logarithmic
periods before taking a negative part. This saves less than 0.08% of the
atomic adverse variation in eleven cases and about 1.67% in the remaining
case. This tests the existing cutoff-grouping mechanism; it proves no new
cost estimate or asymptotic rate.

These are **tiny constructed subsets**, not the full core, random
population samples or a density estimate. The adverse cutoff set is chosen
on each entire constructed subset; it is not the unavailable full-core
adverse set. Counts 56+, the many-bin frontier and the eventual Lean order
threshold `N>=65536` are not tested. Primality uses SymPy's numerical
procedure rather than Lean certificates, and all real calculations are
floating rather than interval proofs. Period boundaries use the
piecewise-constant log interpolation of the actual divisor columns.

The amplitudes are rescaled by a common positive factor to avoid numerical
underflow. If the recorded logarithmic amplitude scale is `b`, the actual
subset linear sum is `exp(b)` times the displayed sum and its energy is
`exp(2*b)` times the displayed energy. Thus **none of the displayed energy
values can be compared with the native sufficient budget**
`3/(320*(N+1))`; there is also no transfer from a subset's energy to that
of the full population.

The outcome is diagnostic: reflection supplies useful signed information,
but these tests do not provide a global cancellation estimate. No new
Lean theorem, numerical floor margin or zero exclusion is claimed. The
next substantive estimate remains a bound on the whole retained signed
sum or energy, rather than another phase-band credit identity. Results and
scope controls are recorded in `riesz-reflected-phase-probe-audit.json`.
