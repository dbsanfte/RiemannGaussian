# What the quantitative Gaussian estimate can and cannot supply

The existing Gaussian–Möbius argument gives an exponential saving in a
parameter `h`, but its arithmetic remainder grows exponentially in `h^3`.
`MoebiusCubicRateAudit.lean` now checks the resulting limitation uniformly
over parameter choices. **The audit does not improve the signed-work bound
or exclude a new zero. It prevents treating a subexponential coefficient
gain as a fixed power improvement.**

The actual contour center is

```text
A(h) = 10^15 * h^3.
```

For a complex Mellin weight `s` with `0<Re(s)<1`, the already proved
all-cutoff upper bound has exactly the form

```text
U_s(X,h) = C_s * exp(-h/2) * X^(1-Re(s)) + D_s * exp(A(h)),
C_s = moebiusFiniteCancellationConstant * (1+norm(s)/(1-Re(s))),
D_s = 1+norm(s)*moebiusMellinDerivativeMass(s).
```

Both original coefficients are retained. In its application to the finite
Möbius prefix, `X=M+1`. The rate theorem has a common lower threshold for
`h`, at least `22`.

## Uniform optimization audit

For each `a<1-Re(s)` and each real coefficient `B`, Lean proves

```text
B * X^a < U_s(X,h)
```

for all sufficiently large `X`, **simultaneously for every `h>=0`**.
Choosing a parameter past the usual cutoff does not escape this comparison:
the complete `exp(A(h))` remainder is still present.

The elementary mechanism is that `exp(A(h))<=X` forces `h<=e*log(X)` for
every fixed `e>0`, uniformly in admissible `h` once `X` is large enough.
Thus `exp(-h/2)` cannot provide a fixed negative power of `X`. When
`exp(A(h))>X`, the additive remainder is already larger than `X`.

The analogous square-root envelope satisfies

```text
B * X^a < C * sqrt(X) * exp(-h/2),             a<1/2, C>0,
```

eventually, uniformly over `h>=0` with `exp(A(h))<=X`. This is a comparison
of candidate envelopes, not a newly proved estimate for Suzuki work, and
it transfers no source exponent from the separate eta family.

## A finite-scale test

The audit also proves a comparison without an unspecified large-`X`
threshold. If

```text
h>=22,
exp(A(h))<=X,
B<=C,  C>=0,
b-a >= 1/968000000000000000,
```

then

```text
B * X^a <= C * X^b * exp(-h/2).
```

The exact denominator is `2*10^15*22^2`. Under these explicit conditions,
no admissible finite cutoff makes this envelope strictly smaller than
the source comparison. The proof keeps all coefficient conditions;
it does not assert they hold for an unspecified zero or work estimate.

## Consequences for the current search

This does not rule out stronger cancellation in the actual Möbius sums,
relative savings when the source and envelope have the same cutoff power,
or useful finite windows outside the stated finite-scale conditions.
In particular, it does not prove that every Gaussian method fails.

It does show why propagating this existing absolute-value estimate through
another long chain cannot automatically produce a logarithmic signed
floor. The remaining arithmetic target must use more of the signed
correlation between the next von-Mangoldt atom and the old weighted mass.
The [product-cutoff decomposition](suzuki-product-cutoff-obstruction.md)
keeps the entire triangular interaction and positive convexity reserve
available for that purpose. No independent bound for that correlation
has been found in this slice.

A literature check also found no proved replacement bound in Suzuki's
finite-interval operator construction. That work proves reality of zeros
of finite characteristic functions, but the proposed limiting formula
that implies RH remains conditional and requires control of the arithmetic
terms and spectral shifts. It is therefore a research lead, not an input
that closes our inequality. [Suzuki, Corollary 1.6 and its discussion](https://arxiv.org/html/2606.09096v1#S1.SS2).

Key compiled declarations:

- `moebiusCubic_rateEnvelope_ge_lower_power_of_gap`
- `moebiusCubic_admissible_height_le_log`
- `moebiusCubic_rateEnvelope_dominates_lower_power`
- `moebiusCubic_fullEnvelope_dominates_lower_power`
- `moebiusFiniteMellin_cubic_majorant_dominates_lower_power`
- `moebiusCubic_sqrtEnvelope_dominates_source_power`

The module is imported by the root library. Validation is local, with
commits held under the standing user instruction.
