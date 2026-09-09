# Global moment bounds for the differential zeta response

The [prime/composite pole-order separation](zeta-moebius-wronskian.md)
now has a checked global moment estimate on an explicit complex disc.
The prime contribution is uniformly bounded at the double-pole geometric
scale. After the full source normalization it tends to zero with an
allowance `C/(N+1)`. The composite contribution retains the full nonzero
complex source with the same order of error.

This closes the analytic remainder estimate for these actual filtered
responses. It does not prove an independent upper bound for the composite
source itself or a new zero exclusion.

## A finite weight from the actual divisors

For a hypothetical zero `rho=beta+i*gamma`, `beta>1/2`, choose

\[
s_0=3/2+i\gamma,\quad u=s_0-\rho=3/2-\beta,\quad
R=5/4-\beta/2=(u+1)/2.
\]

`zetaWronskianMomentRadius_spec` proves `0<u<R<1`. The closed disc
`K=closedBall(s_0,R)` stays strictly to the right of one half.

For the actual meromorphic responses `J_rho` and `P_rho`, the common
weight `W_rho` includes, at every point of `K` except `rho`, enough copies
of `(s-z)` to cancel the negative orders of both divisors. Compactness
proves its support finite. The selected exponent is zero, so
`W_rho(rho)!=0`. No nearest-zero assumption, zero-free boundary, numerical
list of zeros, or unproved cancellation premise is used. Every pole in
the disc is treated; this includes the full pole at one if it lies there.

`MeromorphicPairPoleClearing` proves these statements for a general pair
of meromorphic functions. Its explicit normal-form representative of
`(s-rho)^2 W_rho(s) f(s)` is analytic on a neighborhood of every point of
`K`, including former poles and boundary points. The punctured equality
with the raw expression is retained.

## Exact pole division and the uniform error

For an analytic numerator `A`, exact divided differences give

\[
\frac{A(s)}{(s-a)^2}
=\frac{A(a)}{(s-a)^2}+\frac{A'(a)}{s-a}
+\operatorname{dslope}(\operatorname{dslope}(A,a),a)(s).
\]

`div_sub_sq_eq_dslope` and `signedTaylorMoment_div_sub_sq` preserve this
full complex decomposition. Cauchy's estimate bounds the analytic
remainder on the complete closed disc. Because `|s_0-a|<R`,
`exists_doublePoleMoment_uniform_error` proves

\[
\left|(s_0-a)^{N+2} M_N\!\left(\frac{A}{(\cdot-a)^2}\right)(s_0)
 -(N+1)A(a)\right|\le C\quad\text{for every }N.
\]

The finite constant may depend on the actual disc and function; it is
independent of `N`. This is an existence bound, not a computed numerical
constant or a zero-location certificate.

## The actual prime and composite estimates

Write `J_N=M_N(W_rho J_rho)(s_0)`, with `P_N,Q_N` defined using the
identical weight, and put

\[
c_\rho=W_\rho(\rho)\,m^3\operatorname{lead}_{\rho}\zeta\ne0.
\]

The terminal theorems in `ZetaMoebiusWronskianMoments` prove

\[
|u^{N+2}J_N-(N+1)c_\rho|\le C_J,\qquad
|u^{N+2}P_N|\le C_P,\qquad Q_N=J_N-P_N.
\]

In particular, `exists_zetaWronskianPrimeMoment_decay_bound` and
`exists_zetaWronskianCompositeMoment_decay_bound` give

\[
\left|\frac{u^{N+2}P_N}{N+1}\right|\le\frac{C_P}{N+1},\qquad
\left|\frac{u^{N+2}Q_N}{N+1}-c_\rho\right|\le\frac{C_Q}{N+1}.
\]

The corresponding `tendsto` theorems establish both limits. After dividing
by `c_rho`, the real part of the normalized composite response tends to
one and eventually exceeds one half:
`tendsto_zetaWronskianCompositeMoment_aligned` and
`zetaWronskianCompositeMoment_eventually_aligned`.

The error tending to zero is the error around the composite source.
The normalized composite response itself tends to `c_rho`, not to zero.
An independently proved upper bound strictly below one for its aligned
real part, at sufficiently late indices, would supply the missing
contradiction. Such a bound has not been proved.

## Literal arithmetic and the stronger structural connection

The `hasSum_zetaWronskianFullMoment`, `_PrimeMoment`, and `_CompositeMoment`
theorems identify all three responses with genuine convergent arithmetic
sums. Their common kernel includes every cofactor derivative and every
factorial logarithmic term. The prime arm's bound applies to the literal
prime restriction of this kernel.

The subsequent [positive composite convolution](zeta-positive-composite-response.md)
moves one derivative factor inside the signed Möbius sum, obtaining
nonnegative arithmetic coefficients and a universal zeta-zero coefficient
`-m^2`. Its exact moment bridge retains the remaining cofactor. This
provides a new arithmetic structure for attacking the still-open signed
bound; it does not assert positivity after an arbitrary complex filter.

## Local verification

`MeromorphicPairPoleClearing`, `AnalyticDoublePoleMoments`, and
`ZetaMoebiusWronskianMoments` are root imports. The local checks cover direct
warnings-as-errors elaboration, focused and full builds, whole-project
lint, root-imported module lint and all public-theorem axiom audits, and
source and whitespace checks. Work remains local under the user's hold.
