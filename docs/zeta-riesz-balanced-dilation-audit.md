# Balanced-pair prime-dilation test

This test rejects one proposed cancellation mechanism. It proves **no new
saving against the signed `399/5000 = 0.0798` target**. The current balanced
pair defect, every previous payment and the independent floor remain unchanged.

The [Kátai orthogonality criterion](https://www.aimsciences.org/article/doi/10.3934/dcds.2019108)
requires small correlations between distinct prime dilations. For the actual
character `chi_y(n) = exp(-i y log n)`, the optional checked audit instead proves

\[
\chi_y(pn)\overline{\chi_y(p'n)}
=\exp\!\left(-iy(\log p-\log p')\right),
\qquad p,p',n>0.
\]

`unweighted_cross_norm` proves that the correlation over `1 <= n <= X`
has norm **exactly `X`**, at every height. Its phase supplies no orthogonality.

This remains true after retaining the actual balanced factorial weights.
Let `a_(N,p)(q)` be the real amplitude of the literal source-normalized
`selbergDefect * zetaPrimeLogKernel` atom. `literal_atom_eq` proves its exact
phase factorization. On the already-proved untouched balanced block,
`balanced_amplitude_pos` proves `a_(N,p)(q) > 0` for `N >= 65536`.
`balanced_literal_cross_eq` consequently proves

\[
\left|\sum_q a_{N,p}(q)\chi_y(pq)
 \overline{a_{N,p'}(q)\chi_y(p'q)}\right|
=\sum_q a_{N,p}(q)a_{N,p'}(q).
\]

The full positive overlap survives. `relative_cross_cost_ge_one` makes the
negative verdict quantitative: a proposed relative correlation cost `epsilon`
must satisfy `epsilon >= 1` whenever that overlap is positive.

The optional factorial/log-coordinate probe checks 28 cases at native-sized
orders through `4194304`, heights 54 and 100, and quadrature orders 32 and 64.
Its smallest normalized row correlation is approximately `0.999999999999489`;
its effective Gram rank is within `2e-13` of one. The moving Riesz length,
original balanced coefficient and full factorial kernel are retained. These
are floating-point log profiles, **not actual-prime enumeration, prime-density
transport, an interval certificate or a signed arithmetic estimate**. They
earn zero floor credit.

This does **not** rule out cancellation in the original signed pair sum.
The outer prime phases can still cancel; this audit only rejects obtaining
that saving automatically from small prime-dilation/cofactor correlations.
Nor does it rule out every possible large-sieve or signed-amplitude argument.

The old simple-source calibration at `u = 10001/20000` remains about
`0.07987179703494418`, with unchanged gap `0.00007179703494418` above the
independent target. No contradiction or zero exclusion is claimed.

Run only the focused optional checks during local iteration:

```sh
lake env lean -DwarningAsError=true scripts/CheckRieszBalancedDilation.lean
../.venv/bin/python scripts/probe_riesz_balanced_dilation.py
```

The audit imports the compiled root plus the literal balanced-defect module,
runs namespace linters and checks all its declarations for standard logical
axioms only. It adds no carrier or theorem to the registered library chain.
