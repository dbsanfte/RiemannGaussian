# Signed divisor capacities in the original carrier

The [Lean module](../RiemannGaussian/ZetaRieszSignedSperner.lean) improves
an independent pointwise arithmetic inequality. It applies to the original
Riesz coefficient at every positive cutoff and then to the literal core
with its existing masks. It assumes no zero or simplicity hypothesis.
Both cofinal bounds in the [multiplicity-safe criterion](zeta-riesz-joint-floor.md)
remain open.

The subsequent [six-prime geometry theorem](../RiemannGaussian/ZetaRieszSixPrimeGeometry.lean)
strengthens the six-prime interval further to **[-3,4]** whenever
`2*log n<=3L`. This condition is proved eventually on the original core,
uniformly in height and count ceiling. The lower cost is halved relative
to the original symmetric estimate, and the upper cost is reduced by one
third. The proof and its exact ledger are described below.

## What was lost in the absolute estimate

After taking the two smallest prime differences, the original Riesz
response is an integral of the signed divisor window of the remaining
cofactor. Its prime subsets form an antichain. The older bound used the
largest binomial layer for both Mobius signs.

Let `k=omega(n)`, and define

\[
E_{k-2}=\max_{\substack{0\le j\le k-2\\j\text{ even}}}\binom{k-2}{j},
\qquad
O_{k-2}=\max_{\substack{0\le j\le k-2\\j\text{ odd}}}\binom{k-2}{j},
\]

with an empty maximum zero. Positive Mobius divisors occupy only even
layers and negative divisors only odd layers. The LYM inequality gives

\[
-O_{k-2}\le\sum_{A\in\mathcal A}(-1)^{|A|}\le E_{k-2}
\]

for each actual window antichain. Integrating the exact window over the
least-prime interval and reversing the coefficient sign yields

\[
\boxed{
-\frac{T}{L}\log(p_{\min})E_{k-2}
\le c_L(n)\le
\frac{T}{L}\log(p_{\min})O_{k-2},\qquad T=\log n.
}
\]

`signed_antichain_bounds`, `signedDivisorWindow_bounds`,
`riesz_bounds_minFac` and `coefficient_bounds_minFac` prove this chain.
All divisor endpoints are retained. This uses the existing exact window
identity and does not introduce another carrier.

| Prime count | Old symmetric capacities | New coefficient capacities |
| ---: | ---: | ---: |
| 6 | [-6, 6] | [-6, 4] |
| 8 | [-20, 20] | [-15, 20] |
| 10 | [-70, 70] | [-70, 56] |
| 12 | [-252, 252] | [-210, 252] |

The six/eight constants are evaluated by the Lean kernel. The later rows
illustrate the same binomial definition; no higher-count arithmetic tail
is summed or discarded. Existing stronger four/five-prime results remain
available and are not replaced by this general bound.

## Transfer with the observed phase and signed complement

For comparison with the old allowance, replace only `log(p_min)` by `T/k`.
Write the resulting nonnegative capacities as `A_E,A_O`, and put
`x=cos(y*log n)`. The two charges are

\[
D_-=A_E\max(x,0)+A_O\max(-x,0),\qquad
D_+=A_O\max(x,0)+A_E\max(-x,0).
\]

Then `-D_- <= c_L(n)*x <= D_+`. Each charge is at most the previous
absolute antichain charge. For six-prime labels, `D_-` is exactly two
thirds of that previous charge when `x<=0`; `D_+` has the same saving when
`x>=0`. These are alternative lower/upper estimates, not additive credits.

Let `v_n` be the real part of the **actual** residual atom, including its
unassigned fraction and factorial kernel, and let `w_n` be its unchanged
nonnegative envelope. The retained estimates are

\[
\max(v_n,0)-w_nD_-\le v_n\le\min(v_n,0)+w_nD_+.
\]

`core_subset_bounds` sums these on any selected literal core subset and
retains the entire unselected complex sum. Thus every favorable selected
observation is kept, the original phase is never replaced in the carrier,
and no allocation or physical mask is removed. The theorem is uniform in
height, order and prime-count cutoff. It does **not** control the signed
complement, establish a source-normalized finite constant, or prove a
zero exclusion.

## The actual core cutoff halves the other six-prime side

Reflect the cutoff to `D=T-L`. The core supplies `3D<=T`. Write `a,b` for
the two smallest prime logarithms and `w_1,...,w_4` for the remaining
four, so `a<=b<=w_i`. The exact window displacement has `v=D-s<=D`,
with `0<s<a`.

If two complementary pairs both survived, their weights would each be
less than `v`, so `sum w_i<2v`. A surviving pair also gives
`a+b<=2b<v`. Consequently

\[
T=a+b+\sum_i w_i<3v\le3D\le T,
\]

a contradiction. The six possible pairs are partitioned into three
complementary pairs; at most three survive. The full cofactor is separately
excluded. If the unit divisor is in the window, the antichain property
excludes every other divisor, giving capacity one. Negative Mobius terms
can only decrease the upper window bound. These statements handle the
strict window boundaries without approximation.

Thus `riesz_six_lower_third_le` proves `R_D(n)<=3*log(minFac n)`.
Reflection and the coefficient sign give

\[
\boxed{
-3\frac TL\log p_{\min}\le c_L(n)\le4\frac TL\log p_{\min},
\qquad 2T\le3L.
}
\]

If `M` is the previous mean-prime antichain allowance, the charges become

\[
D_-^{(6)}=M\left(\tfrac12\max(x,0)+\tfrac23\max(-x,0)\right),
\quad
D_+^{(6)}=M\left(\tfrac23\max(x,0)+\tfrac12\max(-x,0)\right).
\]

Both are at most two thirds of the old charge for **every** phase.
`eventually_core_subset_six_bounds` discharges the moving-length condition
on every subset of the original core for `1/2<u<=10001/20000` and all
heights/count ceilings. It retains every favorable selected observation
and every other count exactly, with source normalization and the original
allocation kernel. It can therefore be applied to an already selected
signed rest without using any earlier supply a second time. Its bounds
remain component comparisons, not either numerical cofinal endgame bound.

## Quantitative exploration and remaining target

The optional [probe](../scripts/probe_riesz_signed_sperner.py), with
[recorded output](riesz-signed-sperner-probe.json), samples normalized
prime-log shares at `2/3<=L/T<=3/4`, with largest share at most `0.601`.
It suggested the six-prime interval `[-3,4]` now proved analytically above.
Sampled extrema are not certified extrema, and no prime density or
factorial transport is inferred from them.

An exact rational share calculation attains upper capacity four at

\[
\frac{(2,149200,189530,192440,226300,242528)}{10^6},
\qquad L/T=\frac{739383}{10^6}.
\]

Its reflected finite-difference response is `-1/125000`, giving coefficient
ratio four after removing `T/L` and dividing by the least share. These
shares are not asserted to be logarithms of an actual prime label.

Two further exact rational examples lie nearer the actual core ratios:

| Unnormalized shares | Reflected cutoff | L/T | Coefficient ratio |
| --- | ---: | ---: | ---: |
| (1,80,81,82,83,330), total 657 | 197 | 460/657 | -3 |
| (1,80,81,82,83,84), total 411 | 127 | 284/411 | 4 |

Each ratio divides the coefficient by `(T/L)*leastShare` after normalizing
the shares to total one. They illustrate why further uniform pointwise
improvement requires more restrictions or correlations. They do not
establish sharpness on the actual masked prime population.

Reproduce outside ordinary CI:

```sh
OPENBLAS_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_signed_sperner.py \
  --output docs/riesz-signed-sperner-probe.json
```

The next useful strengthening must use more actual cutoff geometry or
joint divisor-sign correlation to pay additional signed mass. The proved
divergence of earlier absolute allowances is unchanged. This local gain
alone does not supply the independent `-79/1000-o(1)` floor for simple
zeros or the `3/2+o(1)` ceiling for multiple zeros.
