# Sublinear arithmetic price for the whole ceiling

The independent constant ceiling **42/25 remains open**. This slice proves
a smaller height-dependent upper bound for the **whole unchanged** native
`joinedPhysical` carrier. At all sufficiently large heights its new price
is at most **one quarter** of the previous whole-carrier price. It also
proves that optimizing this Fejer degree-price method cannot make the
bound constant.

The proof is
[ZetaRieszCeilingSublinearHeight.lean](../RiemannGaussian/ZetaRieszCeilingSublinearHeight.lean).
The preceding fixed-mask adjacent-order identity and its absolute
mask-jump no-go remain unchanged. No prime population is subdivided and
no masked moment is replaced by an unmasked prime limit.

## Actual global signed input

The previously checked `ZetaRieszCeilingAdaptiveFejer` theorem applies
Fejer positivity to the **entire actual competing divisor**, with every
actual local multiplicity retained. For an exposed right-half zero, put
`u = 3/2-Re rho` and `H = log(|Im rho|+22)`. At every positive integer
degree `d` it proves

```math
m_\rho\le (2u)^{32d}+\frac54\frac{H+11}{d}.
```

There is no sparse-divisor, balanced-phase, numerical zero-count or
Type-II hypothesis. The regular channels are paid in this existing
arithmetic theorem. The exposure premise is retained honestly; this
does not prove simplicity for arbitrary unexposed zeros.

Use the original strip `1/2 < u <= 10001/20000` and the previous height
coordinate `L = log(|Im rho|+2)`. The exact displacement
`H <= L+10` is proved, rather than treating these coordinates as equal.
Choose a single degree for the whole divisor:

```math
d(u,L)=\left\lfloor\frac{\log(L+21)}{64\log(2u)}\right\rfloor.
```

Lean proves `d >= 150*log(L+21) > 0` and
`(2u)^(32d) <= sqrt(L+21)`. Consequently the actual multiplicity satisfies

```math
m_\rho\le B(L)
=\sqrt{L+21}+\frac{L+21}{120\log(L+21)},
\qquad \frac{B(L)}L\longrightarrow0.
```

This is an optimized **arithmetic certificate price**, not a numerical
evaluation of an actual zero or the native prime sum.

## Transfer to the same signed carrier

Let `M_old(L)` be the complete previous `heightCap`, including its
already-proved simplicity range and both Gaussian prices. Set
`M_new(L) = min(M_old(L), B(L))`. The source comparison remains signed:

```math
U_{\rm new}(u,L)=-M_{\rm new}(L)+c_{\rm ret}(u)M_{\rm new}(L)^2.
```

At every eligible actual height, the new signed price is no larger than
the previous one. `eventually_joinedPhysical_signed_ceiling` proves,
for every positive `epsilon`, eventually on the **original** native
dyadic schedule,

```math
\operatorname{Re}\left[u^{N_j+1}
  \operatorname{joinedPhysical}(u,\Im\rho,N_j,K_j)\right]
< U_{\rm new}(u,L)+\epsilon.
```

Every original mask, count, allocation, diagonal and source multiplicity
is preserved through the existing source-transfer theorem. The degree
`d(u,L)` is an auxiliary arithmetic test degree; it is **not** a new
native schedule or a certified carrier entry order.

The old cap retains the lower comparison `M_old(L) >= L/217000` for
`L >= 60001`. Since `B(L)/L -> 0`, it eventually beats any fixed positive
fraction of that cap. The checked polynomial inequality retains the
negative linear prime term:

```math
1\le B\le qM,\quad 0\le q\le1,\quad c>9/10
\quad\Longrightarrow\quad
-B+cB^2\le q^2(-M+cM^2).
```

Thus `exists_quarter_price_native_ceiling` supplies one common height
threshold above which the same whole native carrier has ceiling
`U_old(u,L)/4 + epsilon`. This is a **75% reduction of the old
height-dependent certificate price**, not a reduction of the constant
`42/25` contradiction gap. The threshold is existential; no explicit
all-large-height threshold is numerically certified.

## Stop optimizing this degree price for the constant target

The new lower-price audit covers **every** possible positive degree,
not just the displayed choice:

```math
(2u)^{32d}+\frac54\frac{H+11}{d}
\ge\sqrt{160(2u-1)(H+11)}.
```

For each fixed `u > 1/2`, this tends to infinity uniformly over all
degrees. `eventually_all_degree_prices_gt` proves that every prescribed
constant is eventually exceeded by **all** degree choices.

This is a lower bound on the certificate price. It is **not** a lower
bound on actual multiplicity and does not say the actual native carrier
diverges. It rules out obtaining the constant ceiling merely by tuning
this already-proved degree inequality. Further degree searches cannot
close the target without new signed arithmetic information.

## Quantitative controls and their limits

The optional 360-bit probe compares 24 complete scalar certificate rows
at logarithmic heights `10^3` through `10^10000`, for three radii. An
independent 420-bit replay checks 216 enclosures and relative widths,
including both exact floor inequalities. There are no actual-zero or
prime samples and no native-core enumeration.

The comparison is deliberately candid about scale. At the radius ceiling,
the coarse new cap is still worse than the old one through the tested
height `L = 10^100`; taking the minimum preserves the old price there.
At `L = 10^1000` the new signed price is about `0.61677` of the old
price; at `L = 10^4000` it is about `0.03855`. These are astronomically
large **logarithmic** heights and comparisons of certificate constants.
They do not certify zeros, an entry order, or any fraction of RH progress.

The local leaf, 14 linters and transitive standard-axiom check pass.
All 341 prior proof/probe pins are preserved. See
[the scoped audit](riesz-ceiling-sublinear-height-audit.json).
There is no root registration, public metadata update, wider gate,
subagent, commit or push.

The full original fixed-strip/all-height **constant** ceiling, independent
simple-zero floor and zero exclusion remain open. The active goal is
unchanged. The next decisive estimate still needs actual signed
prime/divisor correlation beyond this complete degree-price envelope;
neither a finer balanced-pair subdivision nor another optimization of
these scalar degree prices is licensed as a closing argument.
