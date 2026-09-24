# All-count continuum cascade and global Abel audit

Continuation from `a8fd37582c65e4578c539a17ad768cdbed078ab2`.
The earlier exact signs, packet embedding, paid core window, five-prime
allocation error and phase audit are unchanged. No short-interval counting
or completion correction is introduced here.

**The strict arithmetic test has not passed.** There is no independent
`1/1000` or `1/500` bound for the actual all-count packet, and no new floor
or zero exclusion. The compiled obstruction is to global Abel transport
using the current pointwise Chebyshev envelope and absolute variation.
It does not show that the actual signed transport error is large, or
that every global use of prime correlations must fail.

## Exact normalization and renewal

`ZetaRieszContinuumCascade` defines the full signed finite-difference kernel

\[
H_S(d;x)=\sum_{A\subseteq S}(-1)^{|A|}
\left(d-\sum_{i\in A}x_i\right)_+.
\]

`kernel_eq_riesz_prime_product` and `coefficient_saturated_prime` check
the normalization against the literal arithmetic coefficient. If the
largest prime is `p`, the squarefree composite cofactor is `a`, and
`log(a)<=L`, then

\[
c_L(pa)=\frac{\log(pa)}L H_{\operatorname{PF}(a)}(L-\log p;\log q).
\]

The sign is **plus**. No hypothetical-zero phase is used in this identity.

`integral_kernel` evaluates the full signed cutoff transform before
integrating over prime coordinates. With

\[
g_{w,z}(x)=\frac{e^{-wx}-e^{-(w+z)x}}x,
\qquad J_r=\int_r^\infty g_{w,z}(x)\,dx,
\]

`countTransform` is the actual iterated functional

\[
\frac1{k!}\int_{x_i>r}\frac{e^{-w\sum x_i}}{\prod x_i}
\left(\int_0^\infty e^{-zd}H_k(d;x)\,dd\right)\prod dx_i
=\frac{J_r^k}{k!z^2}.
\]

The inner and outer integrability obligations are proved for positive
Laplace parameters. The evaluated transforms are absolutely summable over
all nonempty counts. `cascadeTransform_zero` proves

\[
\widehat F_0(w,z)=\frac{e^{J_0}-1}{z^2}
=\frac1{wz},\qquad J_0=\log\frac{w+z}{w}.
\]

The `-1` removes the empty cofactor. This is the exact transform-level
normalization equivalent to the constant-one continuum model. This slice
does not assert a pointwise inverse-Laplace theorem or interchange the
unevaluated signed count sum and every integral without a separate proof.
The model includes cofactor count one. The arithmetic sign identity above
requires a composite cofactor, and the literal packet selects at least
three prime factors. No theorem identifies the unrestricted transform
with that masked arithmetic packet. The selected least-prime band is a
cutoff contrast, rather than the whole constant-one model.

`hasDerivAt_cascadeTransform` proves the cutoff renewal in transform form:

\[
-\partial_r\widehat F_r=g_{w,z}(r)
\left(\widehat F_r+\frac1{z^2}\right).
\]

`cascadeTransform_cutoff_renewal` also proves its integrated version.
The extra `1/z^2` is the empty-cofactor boundary source. A pointwise
renewal without that source applies only away from the corresponding
boundary; it is not the global identity.

## What remains after summing every count

The exponential formula is sensitive to errors in the prime measure.
`zero_cutoff_prime_variation` computes its exact first variation under
`J -> J+e*h` as `(w+z)*h/(w*z^2)`. It is nonzero for `h!=0`.

More directly relevant to a least-prime band, apply the same perturbation
above both cutoffs `a<b`. `cutoff_contrast_prime_variation` gives

\[
\left.\partial_e\bigl(\widehat F_a(e)-\widehat F_b(e)\bigr)\right|_{e=0}
=h(\widehat F_a-\widehat F_b).
\]

`cutoff_contrast_ne_zero` proves the unperturbed transform contrast is
nonzero for `0<a<b`, `w,z>0`. Thus cancellation of the complete continuous
model does not algebraically eliminate an arbitrary shared prime error,
even after summing counts and taking the cutoff contrast. These are
transform variations, not a sign or lower bound for the discrete error.

There is also an explicit surviving interior fibre, rather than just a
global transform response. `interior_variation_fibre` proves, for
`p<=9/16`, `9/500<=v<=11/500`, `3/25<=d<=4/25`,

\[
\frac{H_2(d;1-p-v,v)}v=1.
\]

Once the middle-prime log share `1-p-v` is fixed, the residual share is
`v<2*(3/250)`. With every remaining prime share at least `3/250`,
**exactly one** remaining prime can fit. All higher-count sections of
that same first variation have empty support. This strip lies inside
the requested least-prime share band. It explains why summing all counts
does not automatically cancel every prime-error fibre. The theorem is
an exact Riesz-kernel and support statement; it does not estimate the
signed prime discrepancy there or assert that every literal parameter
falls in this particular strip.

## The literal packet and the finite-order masks

`ZetaRieszFullParityPacket` selects the proposed interior box

\[
\frac{43}{80}\le\frac{\log p_{\max}}{\log n}\le\frac9{16},
\qquad
\frac3{250}\le\frac{\log p_{\min}}{\log n}\le\frac7{250}.
\]

The packet is a filter/suballocation of `coreResponse`. It retains
squarefreeness, the original count cutoff, nondominant and core-window
conditions, the physical prime condition on every leg, `1-boundedShare`,
the full complex kernel, and the exact correlated finite `rectangleMass`.
The latter uses the largest prime, least prime and aggregate remaining
cofactor coordinates; it is never replaced by its limiting indicator.
The least and largest primes are canonical, so there is no pair averaging
or incidence multiplicity. The coefficients remain the original Riesz
coefficients at every count.

`fullParity_direct_ledger` proves exactly

\[
\operatorname{coreResponse}
=\operatorname{fullParityPacket}+\operatorname{fullParityRest}.
\]

`fullParitySelection_bounds` proves this is a suballocation. Neither
summand has an independent signed estimate in this slice. In particular,
this packet is not asserted to equal the former selected triple/five-prime
packet, and no earlier quintuple-only allocation theorem is silently
extended to all counts.

`fullParityBox_count_le` proves `omega(n)<=39`: the largest share is at
least `43/80`, while each of the other shares is at least `3/250`.
Forty primes would require a total share at least
`43/80+39*(3/250)>1`. `fullParitySelection_eq_zero_of_large_count`
therefore kills the entire tail from count 40. Counts 12 through 39
remain in full; their size has not been inferred from a probe stopping
at 10 or 11. No finite-order concentration error is assumed paid.

## Why an O(1/N) relative prime error is not enough for this transport bound

`ZetaRieszCascadeAbelAudit.phase_derivative_cost` proves, for a real
amplitude and a retained fixed phase,

\[
\left|\partial_t\bigl(A(t)e^{-iyt}\bigr)\right|
\ge |y|\,|A(t)|.
\]

The amplitude derivative is real and the phase derivative is imaginary;
they cannot cancel inside that norm. This statement applies before any
prime-count separation and includes the full phase.

For the elementary factorial/Dirichlet test
`t^N exp(-3t/2-iyt)/N!`, the current Chebyshev envelope
`|theta(exp t)-exp t|<=41 exp(t)/(100t)` supplies the standard
absolute-variation allowance `coreAbelAllowance`. Its phase term contains

\[
\frac{41}{100}|y|\int_{1.95N}^{2.03N}
\frac{e^{-t/2}t^N}{N!\,t}\,dt.
\]

This is an allowance computed from an upper bound, **not** a lower bound
on the true Chebyshev error. It is an elementary one-prime test; no theorem
equating it with the complete masked packet's multivariable variation is
asserted. Additional inverse-log factors from prime density change
polynomial costs and require their own bookkeeping.

`coreLogAllowance_lower` proves, already on `[2N,2N+1]` inside the core
for `N>=34`, that the displayed integral is at least

\[
\frac{e^{-1/2}2^N}{6N(2N+1)}.
\]

Consequently `normalized_coreAbelAllowance_tendsto` proves that the
source-normalized allowance tends to infinity for **every fixed**
`u>1/2` and nonzero fixed `y`. Its lower growth rate is a positive constant
times `(2u)^N/N^2`. Shrinking the radius toward one half delays this growth
but does not change the limit. A fixed small continuum residual alone
does not supply the missing geometric saving in this allowance.

## Verdict and next admissible input

The standard one-prime absolute-variation Abel allowance does not give
source-scale `o(1)` from the present pointwise Rosser/Chebyshev relative
error. This remains an estimate-specific negative result, not the complete
multivariable go/no-go test: this slice has not evaluated the variation
after first integrating all the other coupled variables. The exact signed
error after jointly summing counts and variables could be much smaller.
The literal packet bound is neither proved nor refuted.

The next arithmetic obligation is a signed estimate for that actual weighted
prime discrepancy, or an exact identity that cancels its first variation
with independently bounded higher variations. This may require evaluating
the fully coupled variation before applying the prime error envelope.
The required estimate must
retain the literal factorial selection and moving cutoffs. A pointwise
continuum cutoff bound such as `1e-4`, a finite numerical count subtotal,
or a completed-source identity is not that estimate. The pointwise
continuum sensitivity bound and the discrete transfer are both still open.
No stronger short-interval theorem is requested by this audit.

The default RH explorer endpoint, existing zero-free results, numerical
certificate and `LocalizedTypeIIBound` are unchanged.
