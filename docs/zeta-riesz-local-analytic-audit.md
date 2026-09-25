# Finite local xi decomposition and the analytic-factor support obstruction

**The local divisor replacement passes. Stability under an arbitrary analytic
remainder fails.** The counterexample is a toy analytic remainder, not an
identification of the actual zeta remainder. This slice proves no packet
decay, arithmetic floor, or additional zero exclusion.

This continues the [finite-support and infinite-divisor audit](zeta-riesz-negative-mode-support.md)
in the current local tree after `cb88975`. The Gamma-growth obstruction to
fixed ordinary primitives of the global xi count product remains intact.
All previous finite masks, packet/rest ledgers and negative audits remain.
No low factorial orders are deleted.

The subsequent [artificial-mode renormalization test](zeta-riesz-artificial-mode-audit.md)
proves the proposed single-slice interpolation and checks its exact
two-variable lift. It preserves the results here.

The later [joint prime-transfer audit](zeta-riesz-joint-prime-transfer.md)
pays literal share, ownership, allocation, radial and high-count errors.
Its remaining signed counts 3..55 and complementary carrier are still open;
the local analytic decomposition here is not used as an unsupported masked
phase-transfer theorem.

## Genuine local divisor: the positive result

[ZetaRieszLocalXiDivisor](../RiemannGaussian/ZetaRieszLocalXiDivisor.lean)
uses the adaptive radius only, without its reflected canonical modes.
For a genuine right-half zero rho, put u=3/2-Re(rho), s0=3/2+i Im(rho).
In the requested range u<=10001/20000, `normalized_radius_bounds` proves

$$
\frac{1+u}{2}<R<1,\qquad \frac43<\frac Ru<2.
$$

`localDivisor` contains exactly the genuine nontrivial zeros in the open
disk B(s0,R). `selected_mem` includes rho, and `radius_sphere_nonzero`
proves that xi has no zero on its boundary. Each coefficient is exactly
`analyticZetaZeroMultiplicity`; no artificial zero or infinite limit appears.

`exists_localXiLogRemainder` patches the removable singularities of the
finite principal-part subtraction. It produces H analytic throughout the
disk and, away from the divisor, the exact equality

$$
\frac{\xi'}{\xi}(s)
=\sum_{\tau\in S_\rho}\frac{m_\tau}{s-\tau}+H_\rho(s).
$$

`fullGenerating_local` then gives the exact shifted-center full generating
function, subject to its explicit off-divisor and off-pole hypotheses:

$$
\widetilde G(t)
=-\sum_{\tau\in S_\rho}\frac{m_\tau u}{s_0-\tau-ut}+A_\rho(t).
$$

`analyticOnNhd_analyticRemainder` proves A analytic on |t|<R/u.
`analyticRemainder_coefficient_bound` proves an existential height-dependent
Cauchy bound M(3/4)^n. The formal bound uses `signedTaylorMoment`, whose
norm is the Taylor coefficient norm. The same bound is proved separately
for exp(A)-1; it does not bound the product with a singular count factor.

`local_singular_core` applies the existing finite weak inverse theorem to
the actual divisor with repeated indices for every analytic multiplicity.
It vanishes on the stated core-supported tests, retaining the empty-cofactor
term, all diagonal deltas and their derivatives. Thus the finite singular
part itself has exactly the requested support and radius margin.

## Count normalization matters

The meromorphic leg generator is integrated before forming the count
exponential. Exponentiating a meromorphic logarithmic derivative directly
would generally create an essential singularity, not the rational factor
in the finite-mode theorem.

On the normalized path w=1,z=-t, one selected negative leg
Z(t)=-1/(1-t) gives the count factor P(t)=1/(1-t).
For an analytic leg A(t), its normalized count factor H(t)=exp(B(t)) obeys
B'(t)=-A(t), B(0)=0. The mixed term to test is P(t)(H(t)-1).

More generally, if Q and B are analytic at 1,
`analytic_factor_principal` proves the exact simple-pole principal part

$$
\frac{Q(t)(e^{B(t)}-1)}{1-t}
=\frac{-Q(1)(e^{B(1)}-1)}{t-1}
  +\text{a function analytic at }1.
$$

Consequently analyticity of B at 1 does not cancel the source pole.
The residue depends on the integrated remainder's value at 1, not just
its constant Taylor coefficient at 0. In the normalized analytic-leg
convention, if A(t)=sum a_n t^n, this value is
B(1)=-sum a_n/(n+1). Thus even a constant or linear leg changes the
source residue; numerical models below use this normalization explicitly.
For a pole of higher multiplicity,
the corresponding numerator jet must vanish; the existing finite-pole
Taylor regularization gives that criterion. No such identity for the
actual zeta remainder has been proved in this slice.

## Exact counterexample, including the inverse and boundary terms

[ZetaRieszAnalyticFactorAudit](../RiemannGaussian/ZetaRieszAnalyticFactorAudit.lean)
takes the analytic leg

$$
A(t)=\frac1{2-t},\qquad H(t)=1-\frac t2.
$$

This leg is analytic on |t|<2 and satisfies the requested M(3/4)^n
coefficient bound. `toyFactor_derivative` proves its correct primitive
normalization. The mixed count factor is exactly

$$
P(t)(H(t)-1)
=-\frac{t}{2(1-t)}
=\frac12+\frac{1}{2(t-1)}.
$$

`hasSum_toyPerturbation` proves that every positive-order coefficient is
-1/2. `not_eventually_geometric` rules out any eventual coefficient bound
M q^N with 0<=q<1 for this sequence.

A nondecaying univariate coefficient sequence alone is not a support
counterexample: multiplying a supported response by a constant can retain
its support. The decisive theorem is the full two-variable inverse.
Here the analytic count factor and the complete response are

$$
H(w,z)=\frac{w+z+1}{w+1},\qquad
\frac{1-\frac{w}{w+z}H(w,z)}{z^2}
=\frac1{z(w+z)(w+1)}.
$$

`hasSum_toyResponse` derives this from the convergent complete nonempty
count exponential, with every count and the empty-cofactor subtraction
retained. `leakageKernel_transform` evaluates the ordinary one-sided
double Laplace transform exactly, on w>0,z>1. Its inverse on s,d>0 is

$$
K(s,d)=e^{-s}\bigl(e^{\min(s,d)}-1\bigr).
$$

`leakageKernel_below_pos` proves positivity throughout 0<d<s.
At s=9/20,d=3/20, `leakage_inside_core_geometry` proves both

$$
s-d=\frac3{10}>\frac7{25},\qquad
1-s=\frac{11}{20}\in\left[\frac{43}{80},\frac9{16}\right],
$$

and K(s,d)>0. The value is approximately 0.1031900691. This is an ordinary
contribution on an open region below the diagonal, not a delta-channel
convention or a discarded one-sided boundary. The new unshifted denominator
w+1 permits horizontal propagation; local analyticity of the leg does not
force diagonal-only convolution.

The toy remainder is an opposite-sign mode outside the local source disk.
It is permitted by the proposed analytic coefficient hypotheses, but it
has not been asserted to equal A_rho. The conclusion is that those
hypotheses are insufficient. The all-negative finite-family support theorem
is unchanged.

## Reproducible numerical test

The optional probe, excluded from routine CI, runs with

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_analytic_factor.py \
  --output docs/riesz-analytic-factor-probe.json
```

It checks orders 32,128,512,2048,8192 with one selected negative mode and
zero, one or two additional negative modes at normalized nodes 8/5 and 9/5.
It integrates constant, linear, geometric and finite geometric-envelope
analytic legs before exponentiation. It also checks the exact rational
counterexample and, separately, a constant count exponent.

For one selected mode and amplitude 0.1, the limiting mixed coefficients are
about -0.0951626 for the constant leg, -0.0487706 for the linear leg, and
-0.1687621 for A(t)=0.1/(1-3t/4). The exact rational example stays at -0.5.
Additional negative modes multiply these limits by their nonzero analytic
prefactor at 1. A constant count exponent is different from a constant leg;
its pole alone is not evidence of support leakage.

The JSON records the script hash, precision, finite series cutoff and all
samples. These numerical series truncations are exploratory, not certified
error estimates. The Lean counterexample and inverse calculation are exact
and do not use the samples.

## Stop point

This meets the requested stop condition: an arbitrary analytic factor can
create support below d=s, and its mixed count contribution can retain an
exact source pole. The next missing input is a special identity or signed
estimate for the actual combined remainder A_rho at the count-transform
level. A generic Cauchy bound, even on radius two, is insufficient.

No physical-cutoff identification, multiplier-subset estimate, broad packet,
revised rest ledger, independent floor, or zero-free improvement is claimed.
The supported insertion bound exp(-N/100) remains available but is not
promoted to a literal packet bound. The global infinite-mode inversion and
old divergent rest allowance are not reopened.

## Validation

Both new modules are imported by the ordinary root and assigned to the
arithmetic family. The warning-as-error full build, whole-project declaration
lint, placeholder scan and compiled-environment soundness audit pass.
Explicit axiom audits of the local decomposition, support application,
Cauchy bound, principal part, count sum and double inverse use only
`propext`, `Classical.choice` and `Quot.sound`. The public mathematical
frontiers remain unchanged; only the compiled inventory grows.
