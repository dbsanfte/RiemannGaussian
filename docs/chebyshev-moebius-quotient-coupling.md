# Keeping the signed quotient prefixes at their own scale

The information-flow audit found a concrete avoidable loss in
`ChebyshevMoebiusCancellation.lean`: the proof of the factorial tail uses
`|M_mu(n)| <= e*N`, after the upstream theorem has supplied the stronger
pointwise estimate `|M_mu(n)| <= e*n`. The new
`ChebyshevMoebiusQuotientCoupling.lean` retains the divided cutoff inside
each signed block and proves a smaller growing-cutoff allowance.

This improves the actual factorial correction. It does not yet improve the
proved `o(sqrt(N))` bound for Suzuki work or exclude a new zeta zero.

## Exact signed source

Write `F(q)=sum_{1<=k<=q} log(k)` and
`M_mu(n)=sum_{1<=d<=n} mu(d)`. For all natural `N,D`, Lean proves

```text
sum_{D<d<=N} mu(d)*F(floor(N/d))
  = sum_{1<=k<=floor(N/(D+1))}
      log(k) * (M_mu(floor(N/k)) - M_mu(D)).
```

The common lower boundary remains inside every signed difference. No
quotient block, boundary fibre, or sign is omitted. The general weighted
finite transposition is also available as
`sum_high_divided_prefix_transpose`.

The complete original remainder retains this sum together with its two
signed harmonic terms in
`sum_moebiusFactorialRemainder_high_eq_signed_quotient_blocks`. That exact
identity remains available before the downstream absolute estimate.

## Improved allowance

Suppose `D<N`, `Q>=1`, `N/(D+1)<=Q` in real arithmetic, and throughout
`D<=n<=N` the actual prefixes satisfy

```text
|M_mu(n)| <= eF*n,          |H_mu(n)| <= eH,
eF>=0,                     eH>=0.
```

The normalized factorial part has allowance

```text
eF * log(Q) * (2+log(Q)),
```

in place of the earlier `2*eF*F(Q)`. The improvement concerns growth in
`Q`; it is not a claim of a strict numerical improvement for every small
cutoff. It follows because the prefix at `floor(N/k)` costs `eF*N/k`,
while the common boundary costs at most `eF*log(Q)` after normalization.

For `D=floor(N/Q)` and `Q>1`, the full correction satisfies

```text
|moebiusFactorialCorrection(N)|
 <= 4/sqrt(Q)
    + eF*log(Q)*(2+log(Q))
    + 2*eH*(1+log(Q)).
```

Both assumptions are discharged in
`exists_moebiusFactorialCorrection_cubic_quotient_bound`. There is a common
`H>=22` such that, for every `h>=H` and every `N,Q` with `Q>1` and

```text
exp(2*A(h)) <= floor(N/Q),    A(h)=10^15*h^3,
```

the displayed bound holds with

```text
eF=(moebiusFiniteCancellationConstant+1)*exp(-h/2),
eH=moebiusHarmonicCancellationConstant*exp(-h/8).
```

This theorem has no hypothetical cancellation premise: it uses the
repository's existing proved Gaussian Möbius estimates. Its cutoff condition
and the two distinct rates remain explicit.

## Where signs remain important in the wider chain

- The gain proved here preserves the relation between prefix size and
  quotient scale. Its final estimate still takes absolute values of the
  blocks and bounds the two harmonic terms separately. Cancellation between
  these signed quantities remains available in the exact source identity;
  it has not been proved by this estimate.
- In the Suzuki work chain, replacing the full work by its bilinear lower
  bound drops a positive convexity reserve. The existing
  `suzukiFirstTailMassLogWork_eq_bilinear_add_reserve` retains that reserve,
  and `suzuki_signed_work_block_eq_massLog_add_error` connects the full
  signed mass-log sum to the original work with a controlled summable error.
  The mass-log sum is therefore the richer available starting point for a
  signed lower-bound attack.
- The current qualitative work estimate uses
  `suzukiMassLogWork_absolute_sum_div_sqrt_tendsto_zero` and then the
  triangle inequality. It cannot use cancellation between positive and
  negative work events. The original signed sum is still retained; the
  missing step is an independent bound on that sum.
- In the reflected eta branch, the positive leading term is already proved
  for the signed current itself by
  `pairedEtaLeadingFluxSignedPartialSum_scaled_tendsto_of_half_lt_re`.
  Merely reversing a norm inequality cannot remove that established signed
  asymptotic. A contradiction still needs independent arithmetic input.

The module is imported by the root library. Validation is local; the standing
instruction to hold commits remains in effect. No novelty claim is made for
the finite hyperbola identity or the logarithmic estimate.
