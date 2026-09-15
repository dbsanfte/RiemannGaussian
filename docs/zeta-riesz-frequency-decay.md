# A frequency sector with a complete vanishing bound

Lean now pays the growing arithmetic cost of an explicit low-frequency
sector of the actual three-prime and higher-prime sums. The deletion error
tends to zero at the original source normalization, uniformly in height
and across all right-half source radii. The interval shrinks with the order.
**The complementary signed integral and tapered wing remain uncontrolled;
this does not yet give a zero-free region.**

The independent endpoint is
[`norm_nonlinear_sub_high_frequency_universal`](../RiemannGaussian/ZetaRieszFrequencyDecay.lean).
The [previous exact frequency representation](zeta-riesz-signed-frequency.md)
and every original arithmetic mask remain in use.

## The bound, including the arithmetic cost

Write `F_N = nonlinearFrequency P u y N` for the coupled frequency response
of the actual three-prime sum `T3` and four-or-more-prime sum `T>=4`.
For every fixed polynomial filter `P`, every height `y`, order `N`, and
`0 <= u <= 1`, Lean proves

```math
\begin{gathered}
d_N=\frac{3}{8(N+1)}\left(\frac34\right)^N,\\
\left|u^{N+1}\left(T3_N+T{\geq}4_N-
 \frac1{2\pi}\int_{d_N}^{\infty}F_N(\xi)\,d\xi\right)\right|
 \le C(P)(N+1)^2\left(\frac{27}{28}\right)^N\longrightarrow0.
\end{gathered}
```

Here `C(P) = 36 * frequencyTiltMass P (7/16) / pi` is the explicit,
nonnegative fixed-filter cost times the repo's genuinely summable positive
integer envelope at exponent `17/16`. It is independent of `u`, `y` and
`N`. All filter coefficients and factorial shifts are included. The
integrals have ordinary integrability proofs.

The earlier cubic allowance retained finite arithmetic costs `C3+C4`.
`nonlinearFrequencyCost_le` now proves, for every `0 < q < 1/2`,

```math
C_{3,N}+C_{\geq4,N}
 \le 2048(N+1)^5q^{-N}\,\mathrm{frequencyTiltMass}(P,q).
```

The factor `d_N^3` pays this whole bound. Thus the right-hand side of the
new error estimate has no remaining arithmetic premise. The broader
natural interval `0 <= xi <= 3/(8(N+1))` is **not** proved to vanish.
Shrinking the interval is an essential part of the present theorem.

## A family of admissible bandwidths

For any positive radius ceiling `U` and `0 < r <= 1`, the sufficient
condition `2 U r^3 < 1` supplies a tilt `U r^3 < q < 1/2`. The full
allowance on `d_N = 3 r^N/(8(N+1))` is at most

```math
\frac{36U}{\pi}\,\mathrm{frequencyTiltMass}(P,q)
 (N+1)^2\left(\frac{Ur^3}{q}\right)^N.
```

This proves decay even for arbitrary moving heights and arbitrary moving
radii in `[0,U]`. These estimates require no hypothetical zero, exposure
or simplicity premise. The bandwidth condition describes this proved
method; it is not an impossibility result for other signed estimates.

## The remaining source

[`tendsto_high_frequency_add_wing_source`](../RiemannGaussian/ZetaRieszFrequencyDecay.lean)
retains the original exposed-zero hypotheses and the original local range
`1/2 <= u < exp(-2/3)`. With full analytic multiplicity `m`, it proves

```math
u^{N+1}\left(\frac1{2\pi}\int_{d_N}^{\infty}F_N(\xi)\,d\xi+V_N\right)
 \longrightarrow -m+m^2c(u),\qquad
c(u)=\frac{\log(32/15)}{-2u\log u}-\log(17/15).
```

The two unresolved objects are the complete complementary integral,
which retains both nonlinear prime classes and their relative phases,
and the tapered wing `V_N`. Their independent **joint** signed bound is
still needed. The larger radius range of the deletion estimate does not
enlarge the range of this source decomposition. Unrestricted multiplicity
is retained; the source is linear in `m` and the paid harmonic cost is
quadratic in `m`.

## Prime imbalance retained in the complete coefficient

The same slice proves a separate bound for the entire three-prime
coefficient on its original upper-reflection support. For every actual
prime factor `p` of a retained three-prime integer `n`,

```math
|c_L(n)|\le\log n\min\left\{\frac12,1-\frac{\log p}{L}\right\}.
```

[`ZetaRieszPrimeEndpoint`](../RiemannGaussian/ZetaRieszPrimeEndpoint.lean)
proves that the actual largest prime gives the strongest bound in this
one-prime family. Its finite signed floor pays only negative real
observations, with the original source factor and polynomial filter.
**The resulting full negative-phase cost has not been bounded at source
scale.** This full-coefficient bound cannot be substituted for a bound on
one frequency sector: it already includes cancellation between frequencies.

For ordered distinct primes `p < q < r`, put `a=log p`, `b=log q`,
`c=log r`, and `s=a+b+c`. Under `c <= L <= s`,
[`TripleRieszProfile`](../RiemannGaussian/TripleRieszProfile.lean) proves
the exact signed identity

```math
-R_L(pqr)=\min\{a,\ L-c,\ s-L,\ 2L-s\}.
```

The actual annulus also ensures `s < 2L`, so all four margins are
nonnegative there. In the chamber `a+b <= L`, `a+c >= L`, `b+c >= L`,
the response is exactly `-(L-c)`. This exposes the endpoint weight shared
with the wing; it does not prove cancellation between the two sums.

Replacing the largest-prime logarithm by its average `s/3` would lose the
new endpoint improvement: Lean proves
`min(1/2, 2-x) <= 1-x/3` for every real `x`. The actual prime imbalance
therefore remains relevant to the next joint estimate.

## Validation and scope

All three modules belong to the ordinary Lean root. Warning-as-error
compilation, root declaration lint and complete transitive axiom audits
check the slice using only the permitted standard logical axioms. The
optional exhaustive numerical certificate is not rerun.

The [RH explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=frequency-sector-decay)
shows the supporting chain after publication. The default whole-carrier
endpoint and proved zero-free region are unchanged. No historical novelty
claim is made for these auxiliary identities or estimates.
