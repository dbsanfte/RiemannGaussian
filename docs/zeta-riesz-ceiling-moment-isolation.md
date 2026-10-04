# Complete arithmetic moment test for the unchanged ceiling

This local slice proves the **same joinedPhysical ceiling in an additional
isolation sector**, and gives an independent finite-order inequality for
every candidate's actual multiplicity. The full all-height ceiling in the
original fixed strip remains open. No literal carrier, mask, phase, moving
length, diagonal or order is changed.

The proof is in
[`ZetaRieszCeilingMomentIsolation.lean`](../RiemannGaussian/ZetaRieszCeilingMomentIsolation.lean).
It uses complete von Mangoldt arithmetic moments, rather than a thinned
prime population or a hypothetical small-error premise. All previous
positive payments and negative audits are preserved.

## Quantitative result

Write

$$
u=\tfrac32-\Re\rho,\qquad H_y=\log(|y|+22),\qquad
m=\operatorname{analyticZetaZeroMultiplicity}(\rho).
$$

For every order $n\ge0$, if **every distinct actual zero** is more than
$R>0$ from $3/2+i\Im\rho$, Lean proves

$$
\begin{aligned}
m\le {}&(2u)^{n+1}
 +(H_y+11)(u/R)^{n+1}+u^{n+1}\\
 &+160u(H_y+H_0)(n+1)(10u/7)^n
 +(H_y+11)(4u/3)^{n+1}.
\end{aligned}
$$

`multiplicity_le_momentTest` proves this inequality directly. Its terms
pay the complete real-axis moment, competing actual zeros, the zeta pole,
the analytic residual including the real-axis error, and the reflected
channels of the existing local expansion. The selected source remains
exactly $-m$; it is not norm-paid to zero.

The entire multiplicity-weighted local divisor is summed once:

$$
\sum_z m_z\le H_y+11.
$$

This avoids pricing the number of zeros times a separate maximum
multiplicity bound. The local analytic radius exceeds $3/4$; its Cauchy
estimate is taken at $7/10$. **That analytic radius is not the competing-zero
separation $R$.** Orders zero and one are included in the general theorem.

The stronger signed theorem `multiplicity_add_competing_re_le` needs
**no competing-zero gap**. Let $Q_n$ be the exact canonical competing
sum, with actual multiplicity coefficients and the selected mode erased.
It proves

$$
m+\Re Q_n\le (2u)^{n+1}+u^{n+1}
 +160u(H_y+H_0)(n+1)(10u/7)^n
 +(H_y+11)(4u/3)^{n+1}.
$$

This preserves the entire signed competing aggregate instead of replacing
it by its norm. For a multiple candidate in the stated strip and finite
height range, `multiple_forces_signed_counterweight` consequently gives

$$
\boxed{\Re Q_{4096}<-\tfrac15.}
$$

That is an actual finite-order constraint on the opposing zero-mode
cancellation, without an isolation premise. It is not a cofinal ceiling:
the arithmetic term $(2u)^{n+1}$ grows with $n$, so taking $Q_n\to0$
under exposure does not turn this finite test into a contradiction.

## Concrete ceiling payment

Set $n=4096$, $R=11/20$, and retain the original strip

$$
\tfrac12<u\le\tfrac{10001}{20000},\qquad
\Re\rho\ge\tfrac{19999}{20000}.
$$

Under the explicit finite height bound $H_y\le10^{150}$,
`momentTest_lt_nine_fifths` certifies that the displayed test is below $9/5$;
`momentTest_lt_two` retains the multiplicity-two threshold.
The proof uses rational powers in blocks of 64. The real-axis term is less
than $7/4$ and each of the other four terms is less than $1/1000$.
No floating arithmetic is used in the Lean certificate.

The sharper numerical evaluation of the conservative test, with $H_0$
replaced by its proved upper bound four, is

$$
1.5063349520468287348858590081\ldots <2.
$$

Consequently `simple_of_gap_log_height` proves that these actual isolated
zeros have multiplicity one. `eventually_joinedPhysical_ceiling_of_gap`
then transfers that result through the unchanged exact source theorem to
the native dyadic carrier:

$$
\Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
 <\tfrac{42}{25}
\quad\text{eventually}.
$$

The extra separation hypothesis is essential. Exposure alone supplies
some gap greater than $u$, which need not reach $11/20$. The displayed
height bound is finite. This is a simplicity result and ceiling payment,
not exclusion of simple zeros and not an RH contradiction.

## Exact population left by this test

Below the finite height bound, a multiple zero in the original fixed strip
must have a **distinct genuine zero** $\tau$ with

$$
\left|\tfrac32+i\Im\rho-\tau\right|\le\tfrac{11}{20},\qquad
\Re\tau\ge\tfrac{19}{20},\qquad
|\Im\tau-\Im\rho|<\tfrac14.
$$

`multiple_forces_cluster` and `multiple_forces_right_cluster` prove this
obstruction. They assert neither a rightward successor nor a global
rightmost zero. In combination with the preserved Gaussian simplicity
layer, surviving multiple candidates also satisfy

$$
L=\log(|\Im\rho|+2)>60000,\qquad
\frac6{L+60000}<1-\Re\rho\le\frac1{20000}.
$$

The next unresolved problem is a signed estimate for such genuine local
clusters, together with unrestricted heights. The test does not bound that
cluster's signed contribution by assuming that its modes are separated.

## Local validation and optional numerical replay

The leaf compiles. Its scoped check passes all 14 namespace linters and
audits every theorem, including private and automatic helpers, using only
standard Lean axioms. The exact count is recorded in the audit. No project
axiom or placeholder is introduced.

`scripts/probe_riesz_ceiling_moment_isolation.py` records five exact rational
block certificates, the five test terms, and six exploratory separation
rows. These rows sample no primes or zeros and claim no optimality or
native carrier entry order. The independent
`scripts/check_riesz_ceiling_moment_isolation.py` replays the block
certificates with FLINT integer cross-products and the five complete scalar
terms with 400-bit Arb intervals. The resulting interval lies strictly
below $9/5$. It also checks the signed counterweight threshold. The sharper
scalar counterweight requirement is exploratory; the Lean signed theorem
uses the conservative constant $1/5$.

Both tools are optional and outside ordinary builds and CI. Artifacts are
scoped to `.lake/riesz-ceiling-moment-isolation`; the portable audit is
`docs/riesz-ceiling-moment-isolation-audit.json`. Prior source and artifact
hashes are checked without rewriting their bytes. Work remains local,
with no commits, pushes, root registration or wider checks.
