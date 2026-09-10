# Joint arithmetic sieve and smaller Fourier localization

Lean now uses the logarithmic band's lower endpoint to prove an additional
geometric arithmetic-mass bound. This improves the independently controlled
frequency complement for **every dominated complex coefficient family**.
The actual cofinal sieve and its prime-divisor restrictions pass through
the same reduction, retaining the full negative multiplicity source.
The signed bound on the retained interaction is still open.

The [opposite-frequency and reflection identities](zeta-sieved-fourier-reflection.md)
now cancel two physical components exactly within this same retained
interaction. The odd real reflection carries the full source, with no
additional error and no claim of a bound on that surviving work.

## The arithmetic information supplying the gain

Keep the original band and divisor majorant:

\[
\mathcal B_N=\{1\le n\le2^{32N}:\log n>N\log2/4\},\qquad
M(n)=\sum_{ab=n}\log b,
\qquad \mathcal M(\sigma)=\sum_{n\ge1}M(n)n^{-\sigma}.
\]

Lean proves genuine convergence of the last sum for `sigma>1`. For any
complex sequence `a` satisfying `|a(n)|<=M(n)`, the weighted samples are
`a(n)*n^(-5/4)` on the band and zero elsewhere, on the same cyclic group
of order `q_N=2^(32N)+1`. For every `1<sigma<=5/4`,

\[
\sum_{n\in\mathcal B_N}|a(n)|n^{-5/4}
\le
\exp\!\left(-\frac{(5/4-\sigma)N\log2}{4}\right)\mathcal M(\sigma).
\]

The previous Fourier estimate replaced this band mass by the constant
`Mcal(5/4)`. Keeping the lower endpoint supplies the new decay. A convenient
fully checked rational envelope is

\[
\sum_{n\in\mathcal B_N}|a(n)|n^{-5/4}
\le(48/49)^N\mathcal M(9/8).
\]

These bounds hold uniformly over changing coefficient sequences and
arithmetic masks. They use no cancellation or zero assumption.

Compiled entry points in
[ZetaDominatedWeightedFourier.lean](../RiemannGaussian/ZetaDominatedWeightedFourier.lean):

- `sum_norm_zetaArithmeticWeightedSamples_le_exp`
- `sum_norm_zetaArithmeticWeightedSamples_le`
- `zetaArithmeticBand_eq_weighted_pair`
- `zetaArithmeticBand_eq_centered_parts`
- `zetaArithmeticWeightedDFT_sub_zero_eq`

## One analytic condition tests a continuum of rates

Let `f_N` be the existing quarter-line kernel samples, with `f_N(0)=0`,
and let `d(k)=chi(k)-1` be the unchanged cyclic difference symbol. For any
region with `|d(k)|>=delta`, Lean bounds the whole centered pairing by

\[
2\|a_N\|_{\ell^1}\delta^{-2}\|\Delta^2f_N\|_{\ell^1}.
\]

Both terms introduced by centering are included. The existing complete
cyclic difference estimate has the form, for `N>=2`,

\[
\|\Delta^2f_N\|_1\le(8/9)^{N-2}A(p,y)+8(1/2)^NB(p),
\]

where

\[
A(p,y)=C_2(p,y)\sum_{n\ge0}e^{-(9/8)\log n}
 +2\sum_k|p_k|(8/9)^k,
\qquad B(p)=\sum_k|p_k|8^k.
\]

Here `C_2` is `zetaQuarterKernelSecondConstant`. The zero index in the
displayed spatial mass is the existing totalized sampling weight; it
contributes only to this positive allowance. The genuine arithmetic
coefficient at zero is zero. Initial and terminal exceptional cyclic
samples are all included in the difference bound.

For an arithmetic-mass rate `b` and threshold `delta_N=r^N`, the resulting
two geometric rates are

\[
\frac{8b}{9r^2},\qquad\frac{b}{2r^2}.
\]

Thus `b*(8/9)<r^2` controls the entire discarded interaction. Using the
general exponent bound and continuity, Lean proves this for every
positive `r` satisfying

\[
\boxed{\quad r^2>\frac89\exp(-\log2/16).\quad}
\]

Taking `r<1` gives a shrinking retained region. The proof chooses a
strictly convergent exponent `sigma>1` within the available margin;
it never assumes that `Mcal(1)` converges. This is a sufficient rate
criterion, not a claim of optimality for Fourier localization generally.

Compiled entry points in
[ZetaDominatedResonanceDecay.lean](../RiemannGaussian/ZetaDominatedResonanceDecay.lean):

- `tendsto_zetaQuarterGapError`
- `norm_zetaArithmeticCenteredPart_exp_compl_le`
- `exists_zetaDominatedBand_exponent`
- `tendsto_zetaArithmeticCenteredPart_band_rate_compl`
- `tendsto_zetaArithmeticFilter_sub_band_rate`

## Explicit finite-order error for a smaller region

The fixed choice `r=14/15` improves the earlier threshold `(31/32)^N`.
`zetaDominatedResonantModes_subset` proves containment in the previous
region. With `b=48/49`, the two error rates are exactly

\[
\frac{2400}{2401}<1,\qquad\frac{1350}{2401}<1.
\]

Write `T(p)=zetaMoebiusBandTailConstant p`. For `N>=2`, the error between
the actual infinite series and the retained centered pairing is at most

\[
E_N=2^{-N}T(p)+2\mathcal M(9/8)
\left[
\frac{81}{64}A(p,y)(2400/2401)^N+
8B(p)(1350/2401)^N
\right]\longrightarrow0.
\]

This estimate holds before zero-source normalization. The first term
includes both omitted arithmetic tails; the remaining terms include the
complete frequency complement and its centering correction. The first
Fourier rate is close to one: this proves eventual decay, without claiming
a practical small error at modest orders.

[ZetaDominatedMomentBand.lean](../RiemannGaussian/ZetaDominatedMomentBand.lean)
proves summability and the uniform band estimate. In the resonance module,
`zetaQuarterGapError_narrow_eq`,
`norm_zetaArithmeticFilter_sub_narrow_le`, and
`tendsto_zetaArithmeticFilter_sub_narrow` give the exact error and limit.

## The same source has both arithmetic and frequency restrictions

At a hypothetical right-half zero `rho=beta+i*gamma`, keep

\[
u=3/2-\beta\in(1/2,1),\quad
D_N=\lfloor(u^{-1/4})^N\rfloor,\quad
H_N=\lfloor\log_2D_N\rfloor.
\]

Use the original pole-jet polynomial `p` and the
[cofinal sieve](zeta-moebius-growing-sieve.md), which excludes every
product divisible by a mixed-prime factor below `H_N`. Its exact
coefficient `a_N` obeys the original majorant. The smaller retained
interaction is exactly

\[
C_N=\frac1{q_N}\sum_{|d(k)|<(14/15)^N}
\left[\sum_{n\in\mathcal B_N}
a_N(n)n^{-5/4}(\chi(k)^n-1)\right]\widehat f_N(k).
\]

The source theorem is

\[
u^{N+1}C_N\longrightarrow-m_\rho.
\]

There is also a source theorem for every rate in the general analytic
range above. In the original product coordinate, the exact finite sum
uses the original signed coefficient
`c_D(n)=sum_(ab=n,a>D) mu(a)*log(b)` on surviving distinct-prime products,
multiplied by the complete complex physical Fourier weight. Every nonzero
arithmetic coefficient still has

\[
n\ge2(D_N+1),\qquad
pq\ge H_N\quad\text{for every distinct prime pair }p,q\mid n.
\]

The signed source is not inferred from a model or an unconstrained
coefficient sequence: it is transferred from the actual convergent
arithmetic sum. If `L_N` is the original pole-jet response, Lean proves

\[
|u^{N+1}(L_N-C_N)|\le C_\rho(\sqrt u)^N+E_N.
\]

Compiled entry points in
[ZetaSievedFourierCarrier.lean](../RiemannGaussian/ZetaSievedFourierCarrier.lean):

- `norm_zetaMoebiusSievedPrimeCoefficient_le`
- `zetaArithmeticCenteredPart_eq_physical`
- `zetaMoebiusSievedFourierCarrier_eq_physical`
- `norm_zetaMoebiusSievedPrimeFilter_sub_fourier_le`
- `tendsto_zetaRightHalfSievedFourierCarrier`
- `tendsto_zetaRightHalfSievedFourier_band_rate`
- `exists_zetaRightHalfSievedFourier_error_bound`
- `tendsto_zetaRightHalfSievedFourier_physical`

## The signed trigonometric target needs only one strict margin

For the exact unwrapped phase `theta=2*pi*k*n/q_N` and any complex `z`,
Lean proves the half-angle identity

\[
\operatorname{Re}((e^{i\theta}-1)z)
=-2\left[\sin^2(\theta/2)\operatorname{Re}z
+\sin(\theta/2)\cos(\theta/2)\operatorname{Im}z\right].
\]

The actual sieved coefficients are proved real. Applying this identity
inside every retained product therefore gives the exact real work

\[
T_N=\frac1{q_N}\sum_{k\in R_N}\sum_{n\in\mathcal B_N}
a_N(n)n^{-5/4}
\left[\sin^2(\theta/2)\operatorname{Re}\widehat f_N(k)
+\sin(\theta/2)\cos(\theta/2)\operatorname{Im}\widehat f_N(k)\right],
\]

with `Re(C_N)=-2*T_N` and

\[
u^{N+1}T_N\longrightarrow m_\rho/2.
\]

This exposes both channels relevant to a signed estimate. Positivity of
the sine square alone gives no sign for the full work: the arithmetic
coefficients and kernel components are signed, and the mixed term is
present. The earlier exact complex carrier already retained this term;
the new theorem makes it explicit in the real target.

It is enough to prove, for some fixed `epsilon>0`,

\[
u^{N+1}T_N\le m_\rho/2-\epsilon
\]

at arbitrarily late orders. No decay or full complex norm bound is needed.
The factor one half here comes solely from the exact change of coordinates;
it is not an improvement in the source margin. The strict upper bound
remains unproved.

Compiled entry points in
[ZetaSievedFourierTrig.lean](../RiemannGaussian/ZetaSievedFourierTrig.lean):

- `stdAddChar_pow_eq_exp_phase`
- `re_cyclicPhaseAtom`
- `zetaMoebiusSievedPrimeCoefficient_im`
- `zetaArithmeticCenteredPart_re_eq_trig`
- `zetaRightHalfSievedFourierCarrier_re_eq`
- `tendsto_zetaRightHalfSievedTrigWork`

## Remaining obstruction

The full signed interaction `C_N` needs an independent source-beating
inequality. For example, `Re(u^(N+1)*C_N)>=-1/2` at arbitrarily late orders
would conflict with the proved limit and positive integer multiplicity.
That inequality has **not** been proved.

The new result justifies using the arithmetic sieve and a smaller frequency
region together. It does not prove that prime-pair separation gives phase
separation, or that small individual Fourier factors give a small sum of
their kernel products. The earlier failure of the fractional absolute-kernel
allowance remains in force. The next useful cancellation must act on the
retained signed products, for instance by retaining complete divisor fibres
inside this restricted physical weight.

No additional zeros are excluded. The proved edge margin remains
`1/(12*log(|gamma|+22))`; RH remains open. This slice is locally validated
with commits and remote CI held at the user's request.
