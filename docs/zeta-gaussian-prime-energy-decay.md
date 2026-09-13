# Ordinary-prime energy decay at the current dilation

Lean now proves that the complete ordinary Gaussian-prime energy divided
by squared current-region dilation tends to zero at large absolute height.
This holds for moving countable families with bounded nonconstant mass
and first logarithmic frequency cost. The complete auxiliary allowance
also decays, and the original finite-zero source constraint is transported
to the same limit. **The signed boundary budget remains. RH and an enlarged
zero-free region are not proved by this result.**

The two focused modules are
[ZetaEulerPoissonDifference](../RiemannGaussian/ZetaEulerPoissonDifference.lean)
and [ZetaGaussianPrimeEnergyDecay](../RiemannGaussian/ZetaGaussianPrimeEnergyDecay.lean).
They use the already proved log-log region; no external zero-free theorem,
new numerical certificate or unproved arithmetic premise is introduced.

## 1. The height coefficient can be made arbitrarily small

Keep the two height smoothings distinct:

```math
L_{26}(t)=\log(|t|+26),\qquad L_2(t)=\log(|t|+2).
```

The exact signed horizontal Poisson difference is

```math
P(a,r)=\frac{a}{a^2+r^2},\qquad
P(a+h,r)-P(a,r)=
\frac{h\{r^2-a(a+h)\}}
     {(a^2+r^2)((a+h)^2+r^2)}.
```

`atom_difference` retains this numerator. For positive `a` and nonnegative
`h`, `abs_atom_difference_le` proves

```math
|P(a+h,r)-P(a,r)|\le\frac{h}{a}P(a+h,r).
```

Nearby actual zeros use their horizontal clearance `d`. For distant zeros,
`|r|>4`, `0<a<=3` and `h<=1` make the difference nonnegative and at most
`h/r^2`; the reference atom at abscissa `3/2` bounds `1/r^2`.
Writing `X_sigma(t)` for the complete multiplicity-weighted xi Poisson
mass, `abs_mass_difference_le` proves

```math
|X_{\sigma+h}(t)-X_\sigma(t)|
\le\frac{h}{d}X_{\sigma+h}(t)+4hX_{3/2}(t),
\qquad 1\le\sigma\le3,\quad 0<h\le1.
```

The local-gap premise is then discharged for actual zeros.
`exists_eventual_local_gap` uses the existing complete log-log clearance
to supply `d=B/L_26(t)` for every fixed positive `B`, above a
`B`-dependent threshold. Taking `h=c/L_26(t)` gives the checked bound

```math
\left|\operatorname{Re}\frac{\zeta_1'}{\zeta_1}(\sigma+it)\right|
\le
\left(\frac2c+\frac{2+c}{B}\right)L_{26}(t)
+41+4c+\frac{5c}{B},
\qquad \zeta_1(s)=(s-1)\zeta(s).
```

The pole-removed function is understood with its actual filled value at
one. The full regular completion difference is controlled by its already
proved horizontal Lipschitz bound. Choosing `c`, then `B`, then the height
proves `exists_eventual_small_log_bound`:

```math
\forall\epsilon>0\ \exists T_\epsilon\ge2\ \forall\sigma\in[1,3],\quad
|t|\ge T_\epsilon\Longrightarrow
\left|\operatorname{Re}\frac{\zeta_1'}{\zeta_1}(\sigma+it)\right|
\le\epsilon L_{26}(t).
```

This is two-sided and uniform through the Euler boundary. All thresholds
are finite mathematical thresholds, **not numerically evaluated**.
The affine version adds one constant and holds at every height.

## 2. The complete prime energy inherits decay

Use the original amplitudes and full cosine sums from the
[preceding energy module](zeta-gaussian-prime-energy-bound.md):

```math
g_q(v)=\sum_p (\log p)p^{-1-x_q}
 e^{-B_q(\log p)^2}\cos(v\log p),\qquad
Q=\sum_{n\ne0}a_n g_q(\omega_n t)^2.
```

The Gaussian identity keeps the smoothed pole and the pole-removed
response separate before projection. Integrating the affine bound pays
only the Gaussian first absolute moment. The pole and proper-prime-power
remainder have fixed bounds. `exists_uniform_prime_small_log_bound` gives
`|g_q(t)| <= epsilon*L_26(t)` above its own threshold, **uniformly for all
`q>=1`**.

The independently proved total-mass cap `|g_q(v)|<=D*q` is combined with
this small cap before squaring. `exists_uniform_energy_small_log_bound`
proves that one fixed `D>0` satisfies, for every `epsilon>0`, above one
height threshold independent of the family and dilation,

```math
Q\le D\epsilon q\{mL_{26}(t)+F\},\qquad
m=\sum_{n\ne0}a_n,\quad
F=\sum_{n\ne0}a_n\log\omega_n.
```

The hypotheses are nonnegative summable coefficients, `omega_n>=1` away
from index zero and summability of the first logarithmic moment. No
second logarithmic moment, bounded frequency support or phase independence
is required. These are complete prime sums; the theorem does not bound
arbitrary prime subsets selected by their signs.

`tendsto_normalized_fullEnergy_of_bounded_height_ratio` permits the
families, frequencies, height and dilation all to vary. If absolute
height tends to infinity and `m`, `F` and `L_26(t)/q` are bounded, then

```math
\frac{Q}{q^2}\longrightarrow0.
```

This improves the preceding module's requirement `L_26(t)/q -> 0`.
For the actual current dilation,

```math
q(t)=\max\left\{1,\frac{L_2(t)}{320000}\right\},\qquad
\frac{L_{26}(t)}{q(t)}\le320000+\log13.
```

`tendsto_current_dilation_fullEnergy` discharges that geometry. The older
lower ratio bound `320000` beyond the plateau remains true; it obstructed
the older estimate, not the decay now proved by the stronger argument.

## 3. What reaches the actual zero source

Let `S_Z` be the original coefficient-weighted, compensated finite-zero
source, including each selected zero's multiplicity. Let `B_signed` be
the original `signedBudget`, and put `U=max(0,S_Z-B_signed)`. The exact
complete-prime transport already proved

```math
U^2\le(1+1/q)mQ+E(q,m),\qquad
E(q,m)=(1+q)m^2C_{\rm rem}^2.
```

`tendsto_current_source_cost` now proves that this entire right side,
divided by `q(t)^2`, tends to zero. `tendsto_current_source_surplus_sq`
transports it to the actual source:

```math
\frac{\max(0,S_Z-B_{\rm signed})^2}{q(t)^2}\longrightarrow0.
```

Finite zero windows and clipping depths may vary arbitrarily. The source
theorem retains the original nonnegative phase-kernel, anchor, frequency,
scale and clipping hypotheses, alongside the moving-family bounds above.

The remaining signed budget is exactly the clipped left mean plus its
rational correction divided by `2*halfWidth`, the signed Gaussian
completion/pole correction, and the nonconstant right response with its
original factor. None of these terms has been replaced by zero.
A contradiction still needs a proved positive source surplus over that
budget at the relevant scale. Large-height energy decay alone does not
exclude a fixed interior zero, and it does not close the separate centered
prime carrier's independent cofinal signed floor. No historical novelty
claim is made for these classical analytic mechanisms.

The root imports, compiled inventory, family index and **Prime energy**
explorer endpoint include both modules and the actual terminal source
limit. The slice remains local under the current no-commit instruction.

The subsequent [signed-budget reduction](zeta-gaussian-signed-budget-reduction.md)
now proves that the full budget differs from the original clipped left
mean by a term negligible after division by the current dilation. It
retains the right-response multiplier's inverse-square decay. The left
mean itself still needs a source-beating bound; no unclipped limit is
claimed by that reduction.
