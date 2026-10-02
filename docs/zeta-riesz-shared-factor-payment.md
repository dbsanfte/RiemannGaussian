# Pay the large shared-factor cross correlations

This slice proves an arithmetic source-geometric bound for all actual
ordered cross pairs with `log(gcd(n,m)) > N/1000`. It pays this whole
correlation family across every native count, bin, phase and funding
overlap. The remaining smaller-gcd signed cross cost is still open.
No whole numerical floor, ceiling or zero exclusion is proved.

The checked module is
[ZetaRieszSharedFactorPayment.lean](../RiemannGaussian/ZetaRieszSharedFactorPayment.lean),
with focused records in
[riesz-shared-factor-payment-audit.json](riesz-shared-factor-payment-audit.json).
This extends the
[actual diagonal payment](zeta-riesz-diagonal-payment.md).

## The same signed energy

Keep the native source-weighted labels

\[
 w_n=u^{N+1}q_n\operatorname{primeWeight}(A,L,y,N,n,1),
 \qquad H_k(n)=\sum_{d\le k,\ d\mid n}\mu(d).
\]

The original adverse cutoff selection uses the complete funded prefix:

\[
 \mathcal K_-=
 \{k:(\sum_nw_nH_k(n))(f_k-f_{k+1})<0\}.
\]

Define the large-shared-factor part of the actual cross sum by

\[
 C_{\mathrm{large}}=
 \sum_{k\in\mathcal K_-}\frac1k
 \sum_n\sum_{\substack{m\ne n\\\log\gcd(n,m)>N/1000}}
 w_nH_k(n)w_mH_k(m).
\]

`adverseCrossEnergy_eq` proves the exact partition
`C_cross = C_large + C_small`. The second term retains every signed
cross pair not meeting that threshold. The cutoff set is **not**
reselected after the partition. Allocation, phase, factorial kernel,
original physical/count/radial masks and signed funding remain unchanged.

## Actual common-factor sparsity beats source growth

Put

\[
 \sigma=1+1/262144,\quad
 M_\sigma=\sum_{n\ge1}\tau(n)^2n^{-\sigma}<\infty.
\]

For every selected squarefree `S` inside `1..X`, the exact divided label
`n/g` and squarefree coprimality give

\[
 \sum_{\substack{n\in S\\g\mid n}}\frac{\tau(n)}n
 \le\frac{\tau(g)}g\,e^{\log X/262144}M_\sigma.
\]

This is `common_factor_row_bound`. No prime density or uniform
short-interval count is used. The only Dirichlet constants are genuine
convergent masses; no numerical values or finite starting orders are
asserted here.

When `log(gcd(n,m)) > N/1000`, the actual gcd is an admitted common
divisor. Joining the two rows and summing the reciprocal-square tail
gives `large_common_factor_mass`:

\[
 \sum_{\substack{n,m\in S\\\log\gcd(n,m)>N/1000}}
       \frac{\tau(n)\tau(m)}{nm}
 \le
 e^{2\log X/262144}M_\sigma^2
 e^{-N/2000}M_{3/2}.
\]

The exact actual divisor signs and phases are bounded in norm only on
this now-sparse correlation family. Smaller-gcd terms are not norm-paid.

For `|q_n| <= B`, `L >= 1`, `0 <= u <= u_* = 10001/20000` and
`log X <= 3(N+1)`, the original weight bound is

\[
 |w_n|\le B(N+1)(2u)^{N+1}/n.
\]

`shared_source_rate` verifies the uniform exponent audit:

\[
 (2u)^{2(N+1)}e^{(6/262144-1/2000)N}
 \le4u_*^2e^{-N/4000}.
\]

Thus `weighted_largeShared_bound` proves the actual new payment

\[
 |C_{\mathrm{large}}|
 \le C_B(N+1)^3e^{-N/4000},
 \qquad
 C_B=16u_*^2B^2M_\sigma^2M_{3/2}e^{6/262144}.
\]

This is an exponential arithmetic estimate, not another polynomial
improvement to the positive whole-core majorant. It is valid even if
these actual phases reinforce. It does not bound `C_small`.

## The coherent common-cofactor fibres are covered

For actual labels `n=p*a` and `m=q*a`, their gcd is at least `a`.
`common_cofactor_large` therefore places every such pair in the paid
family once `log a > N/1000`.

`cropped_cofactor_large` proves that the original radial window and
owner crop already supply that inequality:

\[
 7N/4<\log(pa),\qquad
 \log p<(60069/100000)\log(pa)
 \quad\Longrightarrow\quad \log a>N/1000.
\]

Consequently the identical-prefix owner fibres in the earlier coherence
audit belong to this paid partition on the cropped native population,
regardless of their cofactor count or bin occupancy. Their columns
have not become orthogonal. The actual reciprocal weights and total
common-factor sparsity supply the saving. The earlier arbitrary-weight
operator counterexamples remain valid.

## The unchanged native floor ledger

Let `P_-` be the original adverse profile energy. It is at most
`4(N+1)`. `weighted_shared_price` proves

\[
 \sqrt{|C_{\mathrm{large}}|P_-}
 \le\underbrace{\sqrt{4C_B}(N+1)^2e^{-N/8000}}
       _{\operatorname{sharedPrice}(B,N)}\longrightarrow0.
\]

`shared_crossCost_split` preserves the entire signed small-shared-factor
aggregate before the final scalar cost:

\[
 \sqrt{\max(C_{\mathrm{cross}},0)P_-}
 \le\sqrt{\max(C_{\mathrm{small}},0)P_-}
      +\sqrt{|C_{\mathrm{large}}|P_-}.
\]

`eventually_joined_small_shared_floor` inserts this into the native
dyadic whole-floor comparison:

\[
 \Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
 \ge-\sqrt{\max(C_{\mathrm{small},j},0)P_{-,j}}
      -\operatorname{err}_j,\qquad\operatorname{err}_j\to0.
\]

The error adds `sharedPrice (4+abs epsilon) N_j` once to the existing
paid errors, including the diagonal payment. The same native unpaid
and paid populations, original favorable selectors, radial tail,
positive supply witness and debit
`tailCost + epsilon + growingDebit` are retained, including overlaps.
No zero hypothesis is used in this arithmetic comparison.

The remaining sufficient floor target is

\[
 \sqrt{\max(C_{\mathrm{small},j},0)P_{-,j}}
 \le79/1000+o(1).
\]

This has **not** been proved or assumed. It requires joint signed
cancellation among weakly sharing labels and the actual funding. A
many-bin occupancy count alone does not prove it. The labels themselves
have not been removed from the carrier; the new payment removes one
cross-correlation family from its energy cost.

## Optional quantitative diagnostic

`scripts/probe_riesz_shared_factor_energy.py` enumerates all selected
actual squarefree integer labels at orders4/5, heights54/65/100. It
forms their actual divisor-column Gram matrix after the original
adverse cutoff selection, then partitions the signed cross entries by
the exact gcd threshold. All observed counts and phases remain joined.
It also records the signed count-pair matrix of the remaining term.

The six tests include four positive and two negative smaller-gcd
aggregates. At these tiny orders the threshold is below `log 2`, so
those remaining pairs happen to be coprime. The common-cofactor terms
are negative in all six tests. Removing a negative large-shared term
can increase the finite cost; the proved geometric error, rather than
a monotonic-cost assertion, justifies the native asymptotic payment.

These supports use `L=11N/8` and exactly empty factorial-allocation
support. They do not certify native moving length, physical primes,
dyadic/count56+ many-bin support or a funding witness. Floats are not
interval certificates or cofinal evidence. The probe remains outside
ordinary builds/CI. All twelve new public proofs pass the focused Lean,
ordinary-root, fourteen-linter and standard-axiom gates. Work remains
local; published endpoints and README are unchanged.
