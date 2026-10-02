# Pay the actual funded energy diagonal

The checked result is an exponential payment for the diagonal of the
**existing** whole-floor sharp-prefix energy. It applies across every
count, bin and phase, including the original signed supply debit. The
signed off-diagonal aggregate still needs an independent arithmetic bound.
The whole floor, ceiling and restricted zero exclusion remain open.

The proofs are in
[ZetaRieszDiagonalPayment.lean](../RiemannGaussian/ZetaRieszDiagonalPayment.lean).
The focused audit is
[riesz-diagonal-payment-audit.json](riesz-diagonal-payment-audit.json).

## Exact cost and the new payment

For an actual finite label set `S`, put

\[
 w_n=u^{N+1}q_n\,\operatorname{primeWeight}(A,L,y,N,n,1),\qquad
 H_k(n)=\sum_{d\le k,\ d\mid n}\mu(d).
\]

Here `q` is the original funding coefficient, including overlaps between
the unpaid population, favorable credits and the same radial supply.
`primeWeight` retains the full allocation factor and actual
`cos(y log n)` phase. No partner labels or prime-density model enter.

Let `f = correctedProfile X L 1 0`, with `X=max(1,max S)`.
The existing energy is exactly

\[
 E=\sum_{k\in\operatorname{activeCutoffs}}
       \frac{\left(\sum_{n\in S}w_nH_k(n)\right)^2}{k}
   =D+C,
\]

\[
 D=\sum_k\frac{\sum_{n\in S}(w_nH_k(n))^2}{k},\qquad
 C=\sum_k\frac{\sum_{n\in S}\sum_{m\in S\setminus\{n\}}
           w_nH_k(n)w_mH_k(m)}{k}.
\]

`phaseEnergy_eq` preserves every signed cross term. Only the diagonal
uses an absolute envelope.

Write

\[
 M=\sum_{n\ge1}\tau(n)^2n^{-3/2}<\infty,
 \qquad u_* =10001/20000.
\]

The repository already proves this summability; its constant is not
numerically evaluated here. On the original `literalWindow`,
`7N/4 < log n <= 9N/4`, the checked `weighted_diagonal_bound` gives

\[
 D\le16u_*^2B^2M(N+1)^3e^{-3N/4},
\]

assuming `|q_n| <= B`, `L >= 1`, `0 <= u <= u_*` and
`log X <= 3(N+1)`. `window_sup_log` proves the last condition directly
from the literal support.

The mechanism is the actual reciprocal-square label weight. In the
window,

\[
 n^{-2}\le e^{-7N/8}n^{-3/2},\qquad |H_k(n)|\le\tau(n).
\]

The remaining radial source factor `(2u)^(2(N+1))` is absorbed into
the fixed exponential gap. This is different from multiplying a
polynomial discount by the positive L1 envelope `(2u)^N`.

The corrected profile satisfies

\[
 P=\sum_k k(f_k-f_{k+1})^2\le1+\log X\le4(N+1).
\]

Consequently `weighted_diagonal_price` and `tendsto_diagonalPrice` prove

\[
 \sqrt{DP}\le
 \underbrace{8u_*B\sqrt M(N+1)^2e^{-3N/8}}_
 {\operatorname{diagonalPrice}(B,N)}\longrightarrow0.
\]

These are actual geometric estimates, independent of occupied-bin
pattern, prime count and height. They do not establish orthogonality or
negative covariance.

## Keep the favorable whole increments uncharged

For the floor, use the existing adverse cutoff set

\[
 \mathcal K_-=
 \{k:(\sum_n w_nH_k(n))(f_k-f_{k+1})<0\}.
\]

This selection is made **after** joining every funded label and count.
Let `C_-` be the signed off-diagonal sum on this set, and `P_-` its
profile energy. The new remaining price is

\[
 K_\times=\sqrt{\max(C_-,0)P_-}.
\]

The only positive part is on this complete signed aggregate. Individual
labels, bins, counts and periods are not separately charged. The exact
energy identity and nonnegative diagonal give

\[
 K_\times\le\operatorname{negativeCost}
 \le K_\times+\sqrt{DP}.
\]

`adverse_crossCost_le` proves the first inequality; the second is used
in `weighted_cross_floor`. Thus the old and new costs differ by at most
the explicit exponentially decaying diagonal price.

## Native whole-floor result

`funded_cross_floor` retains the unchanged weights

\[
 q_n=1_H(n)+a1_{\mathrm{Paid}}(n)+b1_{\mathrm{Tail}}(n)
       -\operatorname{debit}\,1_Y(n),
\]

including every overlap. The credit selectors `a,b` use the actual
signed paid/tail sums; they are not assumed favorable without this
selection. The supply is spent once.

`eventually_joined_cross_floor` plugs this into the native dyadic floor.
It retains the actual unpaid many-bin population, the original paid
counts/bin populations, radial tail, positive supply witness and debit
`tailCost + epsilon + growingDebit`. For the same native witnesses and
an error tending to zero, it proves

\[
 \Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
 \ge-K_{\times,j}-\operatorname{err}_j.
\]

The new diagonal contribution in `err` is
`diagonalPrice (4+abs epsilon) N_j`. All prior paid errors are retained.
No exposed-zero hypothesis is used in this arithmetic inequality.

An independent eventual bound

\[
 K_{\times,j}\le79/1000+o(1)
\]

would close the required floor. Equivalently, a sufficient estimate is
`max(C_-,0)*P_- <= (79/1000)^2 + o(1)`. **This is the remaining target,
not a proved estimate or an assumption hidden in the result.** It must
include the cross correlations with the actual supply and credits.

## What the many-bin condition does and does not supply

Many occupied prime-log bins offer locations for factorization. They
do not themselves bound the weighted contribution of one bin, prove
separated total-label frequencies, or give a sign to the cross term.
The earlier phase and coherence audits remain valid.

The new diagonal bound changes the quantitative target: one need not
demand cross cancellation almost equal to minus the diagonal. The
actual diagonal is already tiny. Positive cross energy may remain,
provided its **whole funded cost** has the required numerical bound.
Conversely, no inverse-polynomial discount on a positive L1 majorant
has become sufficient; the earlier rate audit is not contradicted.

The Matomäki--Radziwiłł factorization method is relevant for its prime
factor extraction, but its averaged estimates do not directly give this
fixed-height hard-masked funded bound. Its separability conditions need
checking against the product-dependent Riesz/factorial/allocation
weights. No external theorem is imported as a Lean arithmetic input.
See the [primary paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf).

## Optional finite diagnostic

`scripts/probe_riesz_adverse_cross_energy.py` enumerates actual integers,
their divisors and all observed counts at orders 4--7 and heights
54/65/100. It keeps the factorial kernel, actual total-label phase and
exact corrected-profile increments. It joins labels before selecting
adverse cutoffs and checks the finite prefix/hinge identity and cost
sandwich numerically.

Seven of twelve tested aggregates have positive cross energy; five
have negative cross energy. Cross-period terms can reinforce or cancel.
This is a diagnostic of the signed quantity, not an asymptotic verdict.

These small supports use `L=11N/8` and have empty original allocation
support. They do **not** certify the native moving length, physical
prime masks, count56+ many-bin population, dyadic schedule or funding
witness. Floats are not interval certificates. The probe is optional
and runs outside normal builds and CI.

No new whole population, numerical floor/ceiling or zero exclusion is
claimed. Work remains local; README and published endpoints are unchanged.
