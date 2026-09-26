# Least-prime duality and the retained signed target

The target remains exactly

\[
u^{N+1}\bigl(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\bigr).
\]

**No bound for that signed difference or for its complementary carrier is
proved in this investigation.** The results below audit possible literature
inputs. They preserve every arithmetic mask and every earlier negative audit;
no conditional input is imported as a theorem about primes.

## What the duality actually cancels

Alladi's identities couple least and largest prime factors through a complete
divisor sum. One example, for `f(1)=0`, is

\[
\sum_{d\mid n}\mu(d)f(P^-(d))=-f(P^+(n)).
\]

The higher identities also couple prime counts. Alladi--Johnson obtain
convergence of `sum mu(n)*omega(n)/n` with a least-prime congruence condition,
with logarithmic estimates. The divisor identities are relevant, but the
published summands do not include our correlated factorial selection,
moving Riesz cutoff or product phase. See
[Alladi--Johnson, equations (1.3)--(1.12) and Theorem 10](https://arxiv.org/html/2410.18259v1).

The issue with substituting the current weights is algebraic before it is
analytic. For two distinct primes `p<q` and arbitrary divisor weight `W`,

\[
\sum_{1<d\mid pq}\mu(d)f(P^-(d))W(d)
=f(p)\bigl(W(pq)-W(p)\bigr)-f(q)W(q).
\]

The first difference vanishes for a constant weight. It does not vanish
for a truncated hinge or factorial kernel. Freezing the outer label retains
these shifted weights inside the divisor sum. Reindexing it does not pay
the new cutoff terms. The existing exact two-small-prime tent identities
already retain analogous differences; they are not missing instances of
unweighted duality.

## An adaptive cutoff does not repair the published rate

Tenenbaum extends least-prime `mu*omega/n` cancellation to prime sets of
natural density. His Theorem 1.1 bounds the sum by an allowance proportional
to

\[
\epsilon^*_{\mathcal P}(y)\log v+\frac1v,
\qquad v=\frac{\log x}{\log y}.
\]

The theorem has additional range and density hypotheses. Proposition 3.1
also gives a nonzero inverse-logarithmic leading term for the unrestricted
sum. These are signed arithmetic results, but do not state a transfer to
our weighted, phased carrier. See
[Tenenbaum, Theorem 1.1 and Proposition 3.1](https://tenenb.perso.math.cnrs.fr/PPP/On-Mobius-series.pdf).

[`ZetaRieszDualityRateAudit`](../RiemannGaussian/ZetaRieszDualityRateAudit.lean)
audits the numerical allowance, even granting a zero density-error term and
allowing **any** moment-dependent auxiliary cutoff. Put `t=log x`, `a=log y`.
If `a>=log 2`, `2a<=t` and `t<=203N/100`, then

\[
(2u)^N\left(e\log\frac ta+\frac at\right)
\ge\frac{100\log 2}{203}\frac{(2u)^N}{N+1},\qquad e\ge0.
\]

For every fixed `u>1/2`, the right side tends to infinity. Thus adapting
`y` cannot make this particular allowance small at source scale. The
theorem concerns an **upper-bound allowance**, not the true error: it does
not prove divergence of the retained signed sum or impossibility of a
stronger weighted duality estimate.

Wang's logarithmic analogue includes `log n`, but is a normalized limit for
`mu(n)*log(n)/n` with a fixed least- or largest-prime set. Its statement does
not supply uniform high factorial moments, the moving Riesz masks or a
power-saving error. See
[Wang, Theorem 1.1](https://arxiv.org/html/2504.16002v1).

## Hybrid Euler--Hadamard comparison

The unconditional hybrid formula retains a product over zeros. Its displayed
sharp-prime-cutoff error includes

\[
\frac{X^{K+2}}{(|s|\log X)^K}.
\]

It is not enough here to hold the evaluation height fixed and let the prime
cutoff grow. With `t=log X`, once `|s|t<=exp(t)`, this displayed envelope is
at least `exp(2t)`, **for every order K**. Lean proves this uniformly in
arbitrary `K(N)`. The literature's implicit constants are not claimed
uniform in `K`. The exact formula with its pole/zero terms retained is not
refuted; neither is a sharper smoothing-specific analysis. See
[Gonek--Hughes--Keating, Theorem 1 and Lemma 1](https://arxiv.org/pdf/math/0511182).

## Quantitative diagnostic and decision

The optional [rate probe](../scripts/probe_riesz_duality_rates.py) and
[report](riesz-duality-rates-probe.json) evaluate only these explicit
allowances, at 50 and 90 decimal digits. They are not prime data or interval
certificates. The Lean limits, rather than the rounded table, certify the
rate obstructions. Run outside ordinary CI:

```sh
python3 scripts/probe_riesz_duality_rates.py \
  --output docs/riesz-duality-rates-probe.json
```

The next arithmetic input must control the **weighted signed divisor
differences with the full phase**, or bound their joint sum before any
absolute-value transport. The cited unweighted/logarithmic results do not
provide that input. No new carrier, public proof frontier, zero exclusion or
accomplishment is introduced here.
