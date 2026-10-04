# Integer spacing and unit weights: a detector gate

The independent `42/25` ceiling for the complete ordinary-prime carrier is
still **open**. This slice checks whether the continuous double-source
control depends essentially on fractional atom weights or a continuous
support. It gives **zero arithmetic ceiling credit**.

The finite quantization geometry and conditional source-stability theorem
are kernel-checked in
[ZetaRieszCeilingIntegerAudit.lean](../RiemannGaussian/ZetaRieszCeilingIntegerAudit.lean).
The full infinite binary count-to-density Abel identification described
below is an analytic argument, **not a new Lean witness theorem**. In
particular, the last Lean theorem retains its moment-comparison premise
explicitly; it does not infer that premise for ordinary primes.

## The exact quantization test

For the existing continuous control, set `u=10001/20000`,
`beta=3/2-u=19999/20000`, fix `|y|>=54`, and set `B=40000`. In integer
coordinates its count density is

\[
\rho(x)=
\begin{cases}
0,&x<e^B,\\
\displaystyle\frac{1-4x^{\beta-1}\cos(y\log x)}{\log x},&x\ge e^B.
\end{cases}
\]

The already-proved positive-density inequality gives `rho(x)>0` above
the cutoff. Moreover

\[
\rho(x)\le\frac{1+4e^{-2}}{40000}<1.
\]

Let `F(x)=integral_0^x rho(v) dv`, with `F=0` on the negative half-line,
and define binary integer atoms

\[
b_n=\lfloor F(n)\rfloor-\lfloor F(n-1)\rfloor,\qquad n\ge1.
\]

Monotonicity and the one-Lipschitz bound imply `b_n in {0,1}`. This is not
rounding an individual weight and discarding its error. The **entire
cumulative count** is rounded, and every finite count telescopes exactly.
The resulting counting function is

\[
G(x)=\lfloor F(\lfloor x\rfloor)\rfloor,\qquad |G(x)-F(x)|<2.
\]

These finite count statements are theorems `roundedAtom_zero_or_one`,
`roundedAtom_sum` and `roundedCount_error_lt_two`. They are not prime-count
estimates.

## Why bounded rounding error cannot kill the source

Keep the original phase and every logged order. For
`s0=3/2+iy`, use exactly

\[
f_k(x)=\frac{u^{k+1}}{k!}(\log x)^{k+1}x^{-s_0}.
\]

The derivative is

\[
f'_k(x)=\frac{u^{k+1}}{k!}x^{-s_0-1}
\left((k+1)(\log x)^k-s_0(\log x)^{k+1}\right).
\]

Abel summation and continuous integration by parts give, with the vanishing
infinite boundary and the zero lower count retained,

\[
\sum_{n\ge1}b_nf_k(n)-\int_1^\infty\rho(x)f_k(x)\,dx
=-\int_1^\infty(G(x)-F(x))f'_k(x)\,dx.
\]

All terms are absolutely integrable: `b_n<=1`, `Re(s0)=3/2`, and the
derivative has one additional inverse power of `x`. Only this bounded
rounding error is norm-priced, not the selected source. The ordinary
factorial Laplace integrals after `x=exp(t)` yield

\[
\left|\sum b_nf_k(n)-\int\rho f_k\right|
\le
2(k+1)\left(1+\frac{|s_0|}{3/2}\right)
\left(\frac{u}{3/2}\right)^{k+1}.
\]

The ratio in the target range is at most `10001/30000<1/2`, a fixed
geometric saving. `roundingPrice_tendsto` proves decay of this stated
price; it does not assert such a small error for the actual prime measure.

Changing variables identifies the continuous integral with the existing
`doubleMoment u y B k`. Consequently the analytic quantization argument
retains its limit `-2`, rather than paying that source to zero. The same
joined evaluator retains the limit

\[
-2+4c_{\mathrm{ret}}(10001/20000)
=1.68051281186022328837\ldots>1.68.
\]

The checked theorem `rounding_error_preserves_reverse_ceiling` proves this
consequence **if** the displayed moment comparison holds. The infinite
integer-series/Abel bridge is not formalized in this leaf and is not
smuggled into that theorem.

The conclusion concerns a binary measure on integers, not the full prime
set. Its Euler product would have composite generators and would not have
the zeta Euler coefficients. It is not a counterexample to the desired
ordinary-prime ceiling or to RH. The exact relations of the **complete**
ordinary-prime set remain essential; generic spacing, positivity and unit
weights supply no demonstrated rescue.

## Finite detector regression and scope

The optional
[probe_riesz_ceiling_integer_gate.py](../scripts/probe_riesz_ceiling_integer_gate.py)
uses enumerable integers with `u=3/4`, `beta=3/4`, `y=54`, `B=8`, and upper
integer cutoff `2^20`. These parameters are **outside the target radius**.
It checks 1,045,597 integer cells, selects 81,554 unit atoms, retains logged
orders `0,1,2,4,8,12,16`, and compares the full complex atom sum with the
independent incomplete-factorial integral. The maximum observed moment
difference is approximately `0.000783996`.

The 32 floor decisions nearest an integer are replayed with 85-digit
arithmetic. This is a sensitivity regression, not a ball certificate for
every floating floor decision. Independent kernel spot checks ensure that
the factorial power is `(log n)^(k+1)`, rather than `n^(k+1)`.

The independent
[check_riesz_ceiling_integer_gate.py](../scripts/check_riesz_ceiling_integer_gate.py)
reconstructs all seven continuous moment rows from the complex incomplete
Gamma function, instead of the producer's finite factorial polynomial. It
also replays all six target scalar prices and rejects any upgrade to
ordinary-prime coverage, an infinite witness or a ceiling certificate.

Separate target rows evaluate only the stated geometric rounding price;
they do not enumerate atoms above `exp(40000)`, use actual primes, certify
an entry order or measure remaining carrier mass. In particular, a small
quantization price is not a small ordinary-prime discrepancy.

The local leaf, namespace linters and transitive-axiom audit pass. No
carrier, literal prime mask, count cutoff, moving length, diagonal,
factorial allocation or phase in the actual proof chain is changed. Prior
payments and negative audits are preserved. No root registration, wider
checks, commit, push or public metadata update is part of this slice.

The next arithmetic estimate must use a constraint specific to the complete
prime measure or its exact signed convolution. Repeating a generic positive
measure/spacing bound would leave the selected double source untouched.
