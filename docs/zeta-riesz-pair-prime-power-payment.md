# Whole quadratic prime-power payment

The retained signed pair quadratic can now be replaced by its full von
Mangoldt counterpart with a proved global error of order `1/N`. This pays
the proper-prime-power correction **including all low logged orders**.
It does not bound the remaining signed main term, prove the `399/5000`
target, or exclude a zero.

The leaf is
[`ZetaRieszPairPrimePowerPayment.lean`](../RiemannGaussian/ZetaRieszPairPrimePowerPayment.lean).
It uses the existing four-slot `harmonicEvaluation`; it introduces no new
carrier, masked completion or prime filter. The exact finite identity
`normalized_finite_quadratic_eq_harmonic` matches the original
`factorialQuadratic` at every order and ordinate.

## The global estimate

Write the two actual complete logged arrays as

\[
a_k=u^{k+1}P_k(3/2+iy),\qquad
b_k=u^{k+1}Z_k(3/2+iy),
\]

where `P_k` is the ordinary-prime logarithmic moment and `Z_k` is the full
von Mangoldt moment. Their exact difference is the proper-prime-power
moment. For `0<=u<=10001/20000`, all heights and all `k>=0`,

\[
|a_k-b_k|\le
\frac{10001}{20000}\,\mathcal M_{3/4}
\left(\frac{10001}{15000}\right)^k,
\qquad
\mathcal M_{3/4}
=\sum_n c_{\mathrm{proper}}(n)n^{-3/4}<\infty.
\]

The convergence is already proved arithmetically using the proper-power
counting estimate. Define the fixed finite price

\[
\mathrm{powerMass}=
\frac{(10001/20000)\mathcal M_{3/4}}
 {1-10001/15000}.
\]

If both arrays have norm at most `C`, `N>=65536`, and
`1/2<=u<=10001/20000`, the exact joined evaluator satisfies

\[
\boxed{\quad
|Q_N(a)-Q_N(b)|\le
\frac{22C}{N}\sum_{k<N+2}|a_k-b_k|
\le\frac{22C\,\mathrm{powerMass}}N.
\quad}
\]

This is `norm_ordinary_sub_mangoldt_quadratic_le`. Its real-part version is
two-sided. The proof bounds only the difference, keeping the main signed.
The trace contributes `2C/N`; the central band contributes `8C/N`; the
successor/prefix contributes at most `12C/N`. In particular, the argument
does not require each factorial leg to have large order. Logged orders
zero and one remain in every exact sum and in the error price.

The array bound is **conditional**: the existing exposed-zero theorems
give one finite `C_rho` for both actual arrays. It can depend on the
selected zero and is not a certified small numerical constant. The
proper-power majorant itself is independent of zero hypotheses and
uniform in height. `exists_exposed_quadratic_power_payment` retains every
analytic multiplicity; it does not assume simplicity. It yields a genuine
source-normalized `O_rho(1/N)` correction, not an independent floor for the
main.

## Connection to the literal target

`finite_quadratic_tendsto` exhausts the ordinary primes at each fixed `N`.
Together with the previously proved **whole symmetric** completion and
the one joined square diagonal, `norm_prefix_sub_mangoldt_le` gives

\[
\boxed{
|\mathrm{prefixPairDefect}_N-Q_N(b)|
\le\mathrm{wholeCompletionBudget}_N
 +\mathrm{squareBudget}_N
 +\frac{22C\,\mathrm{powerMass}}N.
}
\]

Each term tends to zero. No physical prime support is removed by a bare
cofactor-completion shortcut, no count sector is completed separately,
and the older physical low-order payment is not spent again.
`tendsto_prefix_sub_mangoldt` establishes the difference theorem under the
original exposed-zero assumptions, without a simplicity hypothesis.

`exists_native_mangoldt_payment_simple` inserts these three costs **once**
into the original native-order core floor with its existing Selberg and
owner budgets. The exact real phase, integer cutoff `floor(13N/32)`,
moving Riesz length and all four signed slots remain unchanged. It does
not replace the main by a positive norm budget.

This bridge makes the existing integer identity
`Lambda*log + Lambda*Lambda = mu*log^2` applicable to full von Mangoldt
products without an unpaid proper-power correction. That coefficient
identity still has to be used with the actual signed factorial weights;
it is not itself a bound for the weighted central/successor terms.

## Remaining arithmetic problem

The same independent cofinal target remains:

\[
\Re\mathrm{prefixPairDefect}_{N_j}\le399/5000+o(1).
\]

The new payment transfers this target to the **same joined signed** full
von Mangoldt quadratic. No bound for that main has been obtained. In
particular, the hypothetical selected source still exceeds `399/5000`;
the correction must tend to zero and cannot remove that source. The
previous positive-density countertest and all other no-go audits remain
valid. The higher-multiplicity ceiling is also open.

## Focused validation

Only the leaf and its optional focused checker are built:
[`CheckRieszPairPrimePowerPayment.lean`](../scripts/CheckRieszPairPrimePowerPayment.lean).
The checker runs namespace lint and audits every declaration for
project-defined or nonstandard axioms. Prior proof and numerical
snapshots are preserved. No numerical extrapolation enters the payment.

There is no root registration, broader gate, CI run, commit or push in
this slice. The local scoped audit is
[`riesz-pair-prime-power-payment-audit.json`](riesz-pair-prime-power-payment-audit.json).
