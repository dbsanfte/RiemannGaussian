# Actual prime budgets for a four/five signed comparison

The next quantitative candidate uses unspent five-prime positive
contributions to pay the surviving four-prime debit on the **negative
cosine** side. The work below proves its coefficient and actual prime-count
ingredients. It does **not** yet prove that the aggregate supply covers
the debit. The joint `-79/1000-o(1)` floor remains open.

The previous [exponential-head payment](zeta-riesz-four-prime-exact.md)
is unchanged. In particular, every prime of a remaining count-three or
count-four label has logarithm greater than a fixed `delta*N`. This permits
uniform fixed-width prime counting. The original moment, radial window,
length, phase, allocation and signed complement remain in use.

## A concrete positive five-prime credit

Put `T=log n`, `D=T-L`, and define the displayed arithmetic balances

\[
B_L(n)=3T-4L+\sum_{p\mid n}(\log p-D)_+
 -\sum_{\substack{A\subseteq\operatorname{pf}(n)\\|A|=2}}
       \left(D-\sum_{p\in A}\log p\right)_+,
\]

\[
Q_L(n)=\sum_{\substack{A\subseteq\operatorname{pf}(n)\\|A|=3}}
       \left(D-\sum_{p\in A}\log p\right)_+\ge0.
\]

[`neg_coefficient_eq_pair_balance_add_triples`](../RiemannGaussian/ZetaRieszFivePrimePairSupply.lean)
proves, for **every** squarefree five-prime label with `0<L<=T` and
`log p<=L` for all its prime factors,

\[
-\operatorname{Re}c_L(n)=\frac{T}{L}\bigl(B_L(n)+Q_L(n)\bigr).
\]

The proof keeps the complete alternating response through reflection.
The unit and singleton channels are evaluated, all pair deficits remain,
and the triple channel is retained with its positive sign. Physical
saturation proves the fourth and fifth subset levels zero.

On the actual core length range, if the largest prime has log share at
most `1/2`, the five-prime coefficient is nonpositive.
`re_atom_ge_pair_credit` proves the independent signed inequality

\[
\operatorname{Re}f_N(n)\ge
 w_N(n)\frac{T}{L}(B_L(n))_+\bigl(-\cos(yT)\bigr)
 \quad\text{when }\cos(yT)\le0.
\]

Here `w_N=(1-boundedShare)*exp(-3T/2)*T^N/N!` is the original
nonnegative weight. `re_sum_ge_pair_credit` sums this credit while
retaining the **entire signed complementary sum**. This is not a free
reserve: using the credit requires removing those same labels from the
complement, and any supply subsequently spent must be deducted once.

`eventually_unassigned_ge` and `eventually_re_atom_ge_raw_pair_credit`
prove that an arbitrarily small fixed relative fraction of this favorable
fixed-count credit pays the old allocation. No separate absolute
source-envelope error is asserted. The physical and other core masks
still have to be checked for any chosen population.

## Sharp bounds on actual ordinary-prime windows

[`ZetaRieszSharpPrimeWindows`](../RiemannGaussian/ZetaRieszSharpPrimeWindows.lean)
works with the existing finite set of primes `a<log p<=a+h`.
For every fixed `h>0`, `alpha>0`, and `epsilon>0`, it proves eventually,
**uniformly over every `a>=alpha*N`**,

\[
(1-\epsilon)(e^h-1)e^a
 \le\sum_{a<\log p\le a+h}\log p
 \le(1+\epsilon)(e^h-1)e^a.
\]

The corresponding actual prime counts have denominators `a+h` and `a`.
The harmonic mass satisfies

\[
\frac{(1-\epsilon)(1-e^{-h})}{a+h}
\le\sum_{a<\log p\le a+h}\frac1p
\le\frac{(1+\epsilon)(e^h-1)}a.
\]

`eventually_tuple_reciprocal_bounds` combines these for arbitrary finite
products of windows. `ordered_product_injective` proves that ordered
disjoint windows count each actual squarefree product once.
`eventually_signed_box_lower` and `eventually_signed_box_floor` apply the
budgets directly to the unchanged residual atoms, using the retained
coefficient, allocation and cosine together. Their pointwise signed-score
premises are explicit; no population or signed prime-density estimate is
hidden in them.

The threshold is existential and may depend on the fixed window width
and requested relative precision. There is no effective PNT rate here.
These bounds support **relative compensation with a strict surplus**;
they do not revive the disproved generic source-scale Abel transport.

## Quantitative probe and remaining proof

`eventually_core_cutoff_ratio` proves for the actual moving length and
every `39N/20<T<=203N/100`, throughout the restricted radius range,

\[
\frac{693}{1015}\le\frac{L_N}{T}\le\frac{139}{195}
\quad\text{eventually}.
\]

The optional [probe](../scripts/probe_riesz_four_five_capacity.py) compares
the complete positive four-prime coefficient for largest share at most
`601/1000` against the negative five-prime coefficient with every share
at least `1/100` and largest share at most `1/2`. It also tests the smaller
credit `(B_L)_+` proved above. Within each of twelve cutoff-ratio intervals
it takes the pointwise worst coefficient over every relevant hinge before
integrating. The model uses coefficient divided by `T` and the symmetric
ordinary-prime-density measure, with common radial and phase factors omitted.

With two independent Sobol scrambles of `2^19` points, the minimum ratios
in the [recorded diagnostic](riesz-four-five-capacity-probe.json) are about
**1.2988** for the full five-prime credit and **1.1343** for the pair
minorant. These are **uncertified numerical integrals**, not bounds on the
actual carrier. The floating-point identity regression checks the signed
pair/triple formula against all 32 original subsets. It is not a Lean
certificate or a rigorous integration error bar.

The next missing step is a certified finite angular covering and a
comparison of actual prime populations over complete negative-cosine
arcs. It must keep the original radial kernel, pay the interval-edge
losses from the surplus, verify all masks, and prove disjoint supply
spending. Fixed logarithmic widths can depend on the fixed height;
exponentially thin phase cells are not proposed. A positive density
surplus alone does not discharge this step. In particular, the two sides
must be compared with their phase weights before calling the four-prime
sector paid.

Positive-cosine debits, remaining triples and higher counts stay signed.
Neither a whole-carrier floor nor a zero exclusion follows from this slice.

Reproduce the optional numerical diagnostic with:

```sh
../.venv/bin/python scripts/probe_riesz_four_five_capacity.py \
  --output docs/riesz-four-five-capacity-probe.json
```

This probe is outside ordinary CI and is not a proof dependency.
