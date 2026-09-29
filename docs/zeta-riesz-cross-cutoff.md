# A joint bound across separated Möbius cutoffs

The cutoff correlations now have a proved summable decay rate. A single
signed estimate therefore controls an arbitrary finite family of separated
cutoffs, with no factor for the number of periods. It applies to the exact
`cutoffSlope` in the retained prime-period formula. The finite counting
error and the actual coefficient dependence on the cofactor remain open;
neither whole RH endgame threshold is proved.

## Cross-cutoff decay

Put

\[
Q(R,S)=\sum_{d\le R,e\le S}\frac{\mu(d)\mu(e)}{[d,e]}.
\]

[ZetaRieszCrossCutoff](../RiemannGaussian/ZetaRieszCrossCutoff.lean) proves
that one constant `C>0` satisfies, for every `R,S>=1`,

\[
\boxed{|Q(R,S)|\le
 \frac{C}{(4+|\log R-\log S|)^2}.}
\]

The exact common-divisor identity is

\[
Q(R,S)=\sum_{g\le S}\varphi(g)
 \left(\sum_{\substack{d\le R\\g\mid d}}\frac{\mu(d)}d\right)
 \left(\sum_{\substack{e\le S\\g\mid e}}\frac{\mu(e)}e\right).
\]

When `S<=R`, each row supplies inverse-square logarithmic decay. The first
controls `log(R/S)` and the second makes the remaining harmonic row sum
integrable. All excluded-prime costs are averaged using the already proved
divisor-square Dirichlet mass. No prime count is fixed or omitted.

## A whole family costs its squared coefficient energy

Suppose the positive integer cutoffs `R_i` satisfy

\[
|\log R_i-\log R_j|\ge h|i-j|,\qquad h>0.
\]

For each fixed `h`, a single constant `E_h>0` then gives

\[
\boxed{\left|\sum_{i,j\in I}a_i a_j Q(R_i,R_j)\right|
 \le E_h\sum_{i\in I}a_i^2.}
\]

This reuses the repository's finite symmetric Schur theorem from
`RiemannXiSuzukiGramSchur`. The row cost is bounded by the convergent
integer series `sum_(k in Z) 1/(4+h*abs(k))^2`. The constant depends on
spacing, but not on the number of retained cutoffs, their location, or
prime-count content. It is proved existentially and is not numerically
evaluated.

For `M_R(n)=sum_(d|n,d<=R) mu(d)`, the same theorem is transported to the
literal finite integer population:

\[
\boxed{\sum_{Y<n\le X}\left(\sum_{i\in I}a_i M_{R_i}(n)\right)^2
 \le E_h(X-Y)\sum_i a_i^2+
       \left(\sum_i|a_i|R_i\right)^2.}
\]

The rightmost term is the combined integer-floor error. It is displayed,
not assumed small. No subtraction of independent upper bounds is used.

The sharper `exists_separated_cancellation_mean_bound` retains the signs
inside that finite error too. Put

\[
F(d)=\mu(d)\sum_{\substack{i\in I\\d\le R_i}}a_i,
\qquad B=\sum_{d\le\max_i R_i}|F(d)|.
\]

The same second moment is at most

\[
\boxed{E_h(X-Y)\sum_i a_i^2+B^2.}
\]

This is always at least as strong as the preceding bound, since
`B <= sum_i |a_i| R_i`. Opposing cutoffs cancel at each divisor before
the counting error is estimated. The integer floors themselves remain
fully accounted for.

## Connection to the actual retained slopes

The existing prime-period coefficient uses the strict slope

\[
\operatorname{cutoffSlope}(D,n)
 =\sum_{d\mid n}\mu(d)\mathbf 1_{\log d<D}.
\]

`cutoffSlope_eq_prefix` proves exact equality with `M_R(n)` when
`R<exp(D)<=R+1`, including integer endpoints. Thus
`exists_joint_slope_bounds` proves both signed sides for

\[
J=\sum_{n\in S}w(n)\sum_{i\in I}a_i\operatorname{cutoffSlope}(D_i,n),
\qquad -K\le J\le K,
\]

where `S` is any finite selection in `(Y,X]` and

\[
K^2=\left(\sum_{n\in S}w(n)^2\right)
\left[E_h(X-Y)\sum_i a_i^2+
      \left(\sum_i|a_i|R_i\right)^2\right].
\]

`exists_joint_cancellation_slope_bounds` gives the stronger version with
the last square replaced by `B^2`. It keeps the same strict rounding and
all of the same masks and weights.

The population mask and common weight `w` may retain phase, allocation,
factorial weights and clipped endpoints. The cutoff-family coefficients
`a_i` are fixed across that population. The theorem does **not** silently
permit arbitrary coefficients `a_i(n)`. In the literal prime-period
formula those coefficients depend on the cofactor, so their variation and
the matching cutoff correction still require a joint estimate.

## Numerical evidence and remaining target

The optional `scripts/probe_riesz_cutoff_correlation.py --families`
computes both the exact finite arithmetic Gram construction with floating
reciprocals, and actual integer-population second moments. With 16 cutoffs
at log spacing approximately `1/2`, the alternating normalized quadratic
is about `0.07749`; its actual mean over `n<=200000` is `0.07560`.
The equal-positive normalized quadratic is about `1.7429`.
These values motivate retaining the coefficient signs in the next step;
they are not certificates or bounds for the masked campaign carrier.

At nominal half-period spacing `pi/54`, the 128-cutoff probe gives an
alternating normalized quadratic about `0.00653` and actual normalized
mean about `0.00637`; the equal-positive quadratic is about `14.52`.
The cutoffs are rounded integers and their actual minimum log spacing is
recorded. This remains a test of the sharp cutoff family, not of all
the original moving prime-period masks or weights.

For that 128-cutoff probe, retaining the combined coefficient lowers the
normalized finite-error allowance from about `32719.54` to `10.22374`.
This is a substantial improvement to the bound, but the actual mean is
still much smaller. Smoothing the two exterior endpoints with a sine-squared
weight gives an alternating quadratic about `0.004661` and actual mean
about `0.004654`. These tests do not establish decay as the moment order
grows, and their smoothing is not an authorized removal of a literal mask.

The full source-normalized cost still needs control. In particular:

- the combined finite error can be much larger than the observed mean;
- the original prime-period coefficient vector varies with the cofactor;
- the retained constant/first moments and their cutoff correction must be
  bounded together, without counting already-paid sectors again.

The optional `scripts/probe_riesz_owner_modulation.py` tests the exact
unpaid binomial order selection and radial factorial envelope together.
On a sampled cofactor-log interval, the vector variation divided by the
radial coefficient norm is about `2.015` at `N=256` (352 periods) and
`2.168` at `N=8192` (11265 periods). This suggests testing a joint variation
bound for the original owner allocation. Sampled variation is not a
rigorous upper bound. This probe does not include changing prime selections,
their boundary jumps, or a source-scale estimate for the carrier.

The subsequent [owner maximal estimate](zeta-riesz-owner-maximal.md) now
proves total variation at most `2` along the ordered periods and controls
the original owner allocation with moving interval endpoints at a binary-depth
cost. The other coefficient dependence and the source-scale counting budget
remain open.

The whole `-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open for
`1/2<u<=10001/20000`. No zero exclusion or RH proof is claimed.

See the [machine-readable proof and probe audit](riesz-cross-cutoff-audit.json)
and the preceding [literal cutoff-difference bound](zeta-riesz-cutoff-mean.md).
