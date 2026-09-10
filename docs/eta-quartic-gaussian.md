# A signed Gaussian upper estimate for the infinite eta quartic

This slice proves an independent arithmetic estimate for the actual
quartic eta numerator on vertical lines to the right of three quarters.
It does not yet bound the complete normalized reflected source or
exclude a zeta zero.

Write

```text
s = sigma + i*t, f(t) = pairedEtaCore(s), g(t) = eta'(s)
Q(t) = f(t)^2 * conj(g(t)^2 - f(t)*eta''(s))
w(t) = exp(-tau*(t-c)^2), J(t) = f(t)*conj(g(t)).
```

The numerator `Q` is the unchanged arithmetic quartic in
`suzukiEtaSpectralSmoothSource_weighted_im_eq_current`. No finite
Dirichlet cutoff or chosen coefficient family is used in the terminal
estimate.

## Exact phase identity

[ComplexGaussianCurvature.lean](../RiemannGaussian/ComplexGaussianCurvature.lean)
completes the square in the existing signed-current identity before
integration. [EtaQuarticGaussian.lean](../RiemannGaussian/EtaQuarticGaussian.lean)
discharges every analytic premise for the infinite eta function. For
every `sigma > 0`, `tau > 0` and real center `c`, the compiled theorem
`pairedEta_quartic_gaussian_square` says

```text
Re integral w*Q
  = -4 * integral w*(Im J - tau*(t-c)*|f|^2/4)^2
    + tau^2/4 * integral (t-c)^2*w*|f|^4.
```

All four eta factors and their phase correlations remain in this
equality. Only the downstream upper theorem discards the retained
nonnegative square. The Gaussian correction has its original sign and
constant.

The infinite eta function and every fixed derivative have proved linear
growth bounds on each positive vertical line. These imply Gaussian
integrability of the complex numerator, current, square and allowance.
The derivative of the complete weighted current is integrable as well,
so the improper fundamental theorem removes both boundary values. There
is no formal interchange of an unproved infinite sum with an integral.

## Independent arithmetic decay

[EtaQuarticGaussianDecay.lean](../RiemannGaussian/EtaQuarticGaussianDecay.lean)
uses the existing height-adapted prefix and remainder bound for eta,
proved from its literal alternating support:

```text
|eta(s)| <= 6*T^epsilon/epsilon
when Re(s) >= 1-epsilon, norm(s) <= T and T >= 3.
```

After the exact substitution `t = c + y/sqrt(tau)`,
`exists_pairedEta_quartic_gaussian_allowance_bound` proves that for every
`0 < epsilon < 1/4` and `M >= 0` there is `C >= 0` such that

```text
tau^2/4 * integral (t-c)^2*w*|f|^4
  <= C * sqrt(tau)^(1-4*epsilon)
```

for all `sigma >= 1-epsilon`, `abs(sigma)+abs(c) <= M` and
`0 < tau <= 1`. The constant is independent of the line, center and
Gaussian time inside that region. Its construction uses a convergent
Gaussian moment, with no numerical certificate.

`exists_pairedEta_quartic_gaussian_signed_bound` gives the same bound for
`max(0, Re integral w*Q)`. The exponent is positive, so
`tendsto_pairedEta_quartic_gaussian_positivePart_moving` proves decay for
every bounded moving family satisfying those eventual conditions.
`tendsto_pairedEta_quartic_gaussian_positivePart` specializes it to every
fixed `sigma > 3/4` and every fixed center.

## What this does and does not remove

The previous bare-curvature estimate omitted the multiplier `eta^2`
and the conjugation in `Q`. This slice controls their signed combined
effect on the stated range. It does not assert decay of the complex
integral, its absolute value, or its negative part.

The full Suzuki source still multiplies `Q` by the varying complex
weight containing the squared smoothing denominator, completion data
and reflection factor. Those factors cannot be pulled out of this
estimate. Their derivatives and phases can carry the surviving source,
as the earlier through-node mass analysis demonstrates.

The current elementary eta height bound reaches zero decay exponent at
`sigma = 3/4`; it supplies no vanishing allowance on the entire right
half of the zero strip. Improving that arithmetic input or exploiting
the retained negative square may strengthen the range. Transferring a
signed bound through the full weight remains the principal obligation.
No new zero exclusion or proof of RH is claimed.
