# Intersecting divisor complements improve the odd-count costs

[ZetaRieszIntersectingWindow](../RiemannGaussian/ZetaRieszIntersectingWindow.lean)
proves new independent signed inequalities on the actual Riesz coefficient
and its weighted carrier. They apply to every odd count at least seven,
including the unpaid population below the
[logarithmic count threshold](zeta-riesz-log-count-tail.md).
The original phase, allocation fraction, factorial kernel and selected
integer labels remain unchanged. No signed supply is spent.

In units `(log n/L)*log(minFac n)`, the checked coefficient intervals are:

| Prime count | Previous interval | New interval |
| --- | --- | --- |
| 7 | [-10,10] | **[-5,10]** |
| 9 | [-35,35] | **[-35,27]** |
| 11 | [-126,126] | **[-308/3,126]** |

The seven-prime negative coefficient cost is halved; the nine-prime
positive cost falls by 8/35. These are pointwise coefficient improvements,
not corresponding percentage reductions of the whole remaining sum.
Multiplication by the original cosine determines which improvement acts
on each endgame direction. Both whole-sum bounds in the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md) remain open.

## The extra correlation in the existing divisor window

After the exact two-smallest-prime differences, write their logarithms as
`a<=b` and the remaining logarithms as `w_i>=b`. A surviving subset obeys

\[
v-b<\sum_{i\in S}w_i<v,
\qquad 3v\le a+b+\sum_iw_i.
\]

The second inequality comes from the proved reflected core cutoff.
If two surviving subsets `S,T` covered the whole remaining prime universe,
then `sum_i w_i<2v`. Consequently `v<a+b<=2b`. Any surviving `S` with
at least two elements also has weight at least `2b`, a contradiction.

Thus **two such subsets cannot cover the universe**, even when they
overlap and are not complements. This strengthens the geometric premise
of the earlier [complementary-divisor estimate](zeta-riesz-complement-window.md).

For a residual universe of size `k`, take an upper-rank layer of size `j`.
Its complements have size `k-j` and are pairwise intersecting. Mathlib's
proved Erdős–Ko–Rado theorem therefore bounds the original layer by

\[
Q=\binom{k-1}{k-j-1},\qquad k-j\le k/2.
\]

Now take `j=(k+1)/2` for odd `k`. Put `C=choose(k,j)` and let `B` be the
largest binomial layer of the same parity excluding `j`. The existing LYM
inequality keeps all ranks in one budget: if `m` subsets occupy rank `j`,
then the total of that parity is at most `B+(1-B/C)m`. Hence

\[
\boxed{\quad\#\{\text{surviving subsets of that parity}\}
\le B+(1-B/C)Q.\quad}
\]

For seven prime factors, `k=5`, `j=3`, `C=10`, `B=5`, `Q=4`, giving
an initial bound of seven rather than ten. Retaining the interaction
between ranks improves this again. If `t` singletons survive, no surviving
triple can use their coordinates. The triple population is therefore at
most `min(4,choose(5-t,3))`. For every integer `0<=t<=5`,

\[
t+\min\!\left(4,\binom{5-t}{3}\right)\le5.
\]

The full five-element subset cannot survive the same cutoff. This proves
the final seven-prime bound five. The other two rows follow from the
general quota and exact rational arithmetic. Neither parity cost increases.

The literature contains stronger inequalities for intersecting antichains;
the present proof uses only the already checked Erdős–Ko–Rado and LYM
theorems. It does not assume a further intersecting-family theorem or a
prime-density estimate. [Greene–Katona–Kleitman, *Extensions of the
Erdős–Ko–Rado Theorem*](https://onlinelibrary.wiley.com/doi/10.1002/sapm19765511).

## Transfer to the literal signed remainder

`window_union_ne_univ`, `window_layer_card_le` and
`antichain_quota_bound` prove the general finite argument.
`five_coordinate_odd_card_le` and `five_window_odd_card_le` prove the
stronger singleton/triple tradeoff. The existing exact
divisor encoding and two-prime integral then give
`coefficient_odd_bounds`. Reflection at odd total prime count reverses
the sign; that sign is retained in the table and in the phase-sensitive
allowances.

`eventually_core_subset_higher_odd_bounds` applies on **every subset of
the original core**, uniformly in height and count ceiling, for
`1/2<u<=10001/20000`. It keeps every favorable selected observation and
all other counts exactly in the same signed sum. In particular, it may
be used on the exact rest after existing payments without using their
four-prime supply a second time. The lower-count and higher even-count
estimates are preserved separately.

The theorem does not sum the new costs to a finite source-normalized
constant. The remaining independent `-79/1000-o(1)` floor and `3/2+o(1)`
ceiling still require cancellation across the unpaid arithmetic population.
No simplicity hypothesis, RH conclusion or zero exclusion is asserted.

## Optional quantitative exploration

The [probe](../scripts/probe_riesz_intersecting_window.py) evaluates the
complete signed subset hinge on positive integer models of prime logarithms.
Its [recorded output](riesz-intersecting-window-probe.json) uses exact
rational arithmetic; the sampled inputs are not actual prime labels,
and the reported extrema are not certified global extrema.

```sh
../.venv/bin/python scripts/probe_riesz_intersecting_window.py
```

This exploration stays outside routine CI. Lean proves the bounds for
actual squarefree integers independently of the probe.
