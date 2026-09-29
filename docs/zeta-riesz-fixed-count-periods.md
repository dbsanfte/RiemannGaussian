# One signed payment mechanism for many prime counts

The same cancellation theorem now applies to every **fixed** cofactor
prime count. Its concrete application adds the selected 7–55-prime sectors
to both whole `J+C` comparisons. The previous six-prime population is kept
once, and the growing saddle-band credit is unchanged. This does not pay
all integers in those prime-count classes or prove a final numerical bound.

## Common structure

Fix a squarefree cofactor `a` with `k >= 2` prime factors, and vary its
unique largest prime `p` over a complete phase period. The selected cofactors
satisfy

\[
 \frac{203}{500}v<\log a\le\frac{197}{200}v,
 \qquad
 \log q\lev-\frac1{16}-\log a\quad(q\mid a).
\]

The prime interval is

\[
 v-\pi/|y|-\log a<\log p\le v+\pi/|y|-\log a.
\]

For `k <= 54`, the upper cofactor cap is redundant: ownership alone gives
`log(a) <= 54v/55`. The [owner-geometry extension](zeta-riesz-owner-geometry.md)
therefore covers every cofactor satisfying the remaining conditions.

These conditions leave every selected prime below the separately paid
owner band. They imply unique largest-prime ownership; no pair incidences
are averaged, and no label is counted twice. All cofactor primes, including
fixed small primes, remain. For the actual moving Riesz length, the exact
coefficient is

\[
 c_L(pa)=(-1)^{k+1}\frac{-\log(pa)}{L}
 \left[\mathcal R_{\log(pa)-L}(a)-\mathcal R_{\log a-L}(a)\right].
\]

The second cutoff is retained throughout the widened band; it is constant
along each prime fibre. The earlier single-cutoff formula is recovered
exactly when `log(a) <= L`. See the
[saturation-boundary extension](zeta-riesz-unsaturated-periods.md).

Its sign may change. The proof needs bounds on its amplitude and variation,
not a fixed-sign chamber. Three estimates extend automatically with `k`:

1. The Riesz response is bounded by a count-dependent constant times the
   **actual least-prime logarithm**.
2. Fractional prime moments give
   `sum_a log(minFac a)/a <= C_k v` and
   `sum_a 1/a <= C'_k sqrt(v)` for literal cofactor sets.
3. The exact factorial allocation changes by at most
   `20(k+1)*sqrt(N+1)/v` times the change in `log(pa)` along the fibre.

The full prime phase is summed before estimating the coefficient's
variation. At every fixed count and fixed height `|y| >= 54`, for every
`epsilon > 0`, Lean proves eventually

\[
 \left|\operatorname{Re}\sum_{n\in Q_k(v,y)}
 (1-\theta_N(n))c_L(n)K_N(n)\right|
 \le \epsilon\,\frac{\pi}{4|y|}
                \frac{e^{-v/2}v^N}{N!}.
\]

This is uniform across `2N <= v <= 2N+sqrt(N)` at the selected phase peaks.
The theorem checks the original core, count, physical upper cutoff and
nondominant masks. The moving owner belongs to the original finite prime
set. No zero or simplicity hypothesis is used.

The constants and eventual threshold depend on the fixed count. This is
**not** a bound uniform over an unbounded count growing with `N`, and the
right-hand radial weight need not vanish after source normalization.

## Concrete use in both whole estimates

`ZetaRieszFixedCountBand` joins cofactor counts 6 through 54, i.e. total
prime counts 7 through 55. Each is charged at most `1/100000000` of the
common radial unit. Their total debit is at most `49/100000000` of that
unit. Adding the previous six-prime debit `1/100000` still costs less
than `1/90000`.

Both `CheckRieszFixedCountLocal` inequalities pay this combined population.
The previously proved capacity credit has enough slack to preserve the
same `sqrt(N+1)*sourceCredit/16` margin per period. The floor retains the
positive part of the new combined signed observation; the ceiling retains
its negative part. The exact sum is taken before this clipping.

`CheckRieszFixedCountJoint` accumulates disjoint periods across the growing
saddle band. `CheckRieszFixedCountWhole` also retains the sharpened
six-prime reflection costs on the exact unpaid complement. The resulting
whole margin is still

\[
 \left(\frac{M_N\sqrt{N+1}}{16}-\frac18\right)G_N
 \ge\frac{N}{16}G_N.
\]

The global owner debit is spent once. Prior five-prime, triple, six-prime,
small-prime and allocation payments are preserved. A separate theorem
constructs actual seven-prime labels in the added set eventually, proving
that this is a strict enlargement rather than a vacuous selection.

## What remains

The untouched rest includes near-balanced share configurations, labels
outside the cofactor/ownership geometry, incomplete boundary periods,
other radial ranges, and higher counts. The final independent whole floor
`-79/1000-o(1)` and ceiling `3/2+o(1)` remain open. There is no new zero
exclusion or RH contradiction.

The optional smooth-model probe retains the moving length, all Riesz subset
signs and the exact unpaid factorial orders. It shows strong signed-period
cancellation in example counts 7–10. It is not an actual-prime certificate;
the Lean payment uses the proved prime-window estimates instead.

- [All-count fractional cofactor mass](../RiemannGaussian/ZetaRieszCofactorMass.lean)
- [Fixed-count literal signed theorem](../RiemannGaussian/ZetaRieszFixedCountPeriod.lean)
- [Joint count payment and strict enlargement](../RiemannGaussian/ZetaRieszFixedCountBand.lean)
- [Whole floor and ceiling](../scripts/CheckRieszFixedCountWhole.lean)
- [Optional numerical probe](../scripts/probe_riesz_fixed_count_period.py)
- [Verification and cached-cover audit](riesz-central-capacity-audit.json)

The optional applications reuse the already checked cover cache. No
exhaustive numerical cover verification is added to ordinary builds or CI.
