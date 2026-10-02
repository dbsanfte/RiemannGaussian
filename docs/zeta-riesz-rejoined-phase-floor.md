# One signed energy for the retained whole floor

The independent `-79/1000` floor remains **open**. This local slice proves
an unconditional bound for the existing retained aggregate, joining its
unpaid population and funding before squaring. It proves neither an
exponential cancellation rate nor a new source-scale population payment.

Source: [ZetaRieszRejoinedPhaseFloor.lean](../RiemannGaussian/ZetaRieszRejoinedPhaseFloor.lean).
Validation: [proof audit](riesz-rejoined-phase-floor-audit.json).

## Why join on the total integer

For an original label `n = p*a`, the factorial, allocation and phase
weight is exactly independent of the marked prime once that product is
fixed. `primeWeight_product` proves this pointwise. The marker `1` in
`primeWeight(...,n,1)` is an evaluation of the existing total function;
it does not declare `1` to be prime or complete the owner support.

Rejoining the two owner hinges recovers the original total-label Riesz
response. For squarefree nonprime labels,

\[
\operatorname{Re}\bigl(\mathrm{residualCoefficient}(n)K_N(s_0,n)\bigr)
=\mathrm{primeWeight}(n,1)R_L(n).
\]

Both the phase `cos(y log n)` and the literal `1-boundedShare` remain in
this weight. Nonsquarefree labels have exactly zero original coefficient.
Every count, owner, physical, bin and radial mask stays in the original
finite support; no population or prime incidence is completed.

For any support whose labels have at least three prime factors, the
constant and logarithmic divisor profiles vanish exactly. Therefore one
may use the existing affine-log centered profile

\[
f(d)=(L-\log d)_++\sigma\log d
       -\bigl((L-\log X)_++\sigma\log X\bigr),\qquad d\le X,
\]

and zero beyond `X`. The slope is arbitrary. The new weighted prefix
identity allows arbitrary **signed** real population coefficients, rather
than taking norms of separate owners, counts or periods.

## The complete floor, including its funding

Use the same sets as the existing published floor ledger:

- `H = remainingOwnerBand`: the current many-bin growing-count remainder;
- `P`: the retained fixed-count, dense-count and few-bin paid bands;
- `T`: the existing retained radial tail;
- `Y`: the same four-prime radial funding supply.

Let `a,b` be `1` when the complete original signed real sum over `P,T`,
respectively, is nonnegative, and `0` otherwise. These recover **exactly**
the existing ledger's two global positive-part credits. No individual
count, label or period is clipped. With the original relative debit

\[
D_N=\mathrm{tailCost}(c,N)+\varepsilon+\mathrm{growingDebit}(\kappa,N),
\]

put

\[
\alpha_N(n)=\mathbf1_H(n)+a\mathbf1_P(n)+b\mathbf1_T(n)-D_N\mathbf1_Y(n),
\qquad
w_N(n)=u^{N+1}\alpha_N(n)\,\mathrm{primeWeight}(n,1).
\]

Overlaps are kept with these exact algebraic coefficients. In particular,
a funding label that also belongs to a credited population receives its
original credit **and** its original negative debit, not a second credit.
`rejoined_weight_sum` proves this without a disjointness assumption.

Set `U = H union P union T union Y`, `X = max(1,max U)`, and define the
existing signed prefix correlation and two energies:

\[
\Phi_N(k)=\sum_{\substack{n\in U\\n\text{ squarefree}}}
 w_N(n)\sum_{\substack{d\mid n\\d\le k}}\mu(d),
\quad
E_N=\sum_{k\text{ active}}\frac{\Phi_N(k)^2}{k},
\quad
P_N=\sum_{k\text{ active}}k\bigl(f(k)-f(k+1)\bigr)^2.
\]

The unconditional terminal theorem
`eventually_joined_funded_phase_floor` gives, with the **same** funding
witness and vanishing error as the existing ledger, a one-sided cost.
First join the entire signed prefix, then select

\[
K_N^- = \{k\text{ active}:\Phi_N(k)(f(k)-f(k+1))<0\},
\qquad
C_N^- = \sqrt{
 \left(\sum_{k\in K_N^-}\frac{\Phi_N(k)^2}{k}\right)
 \left(\sum_{k\in K_N^-}k(f(k)-f(k+1))^2\right)}.
\]

No individual label, bin, count, owner or period is selected by this sign
test. It acts only **after** all their correlations and funding have been
assembled. Favorable complete cutoff contributions are left uncharged.
The resulting checked bound is

\[
\boxed{
\operatorname{Re}\bigl(u^{N_j+1}\,\mathrm{joinedPhysical}_j\bigr)
\ge-C_{N_j}^--\mathrm{err}_j,
\qquad \mathrm{err}_j\to0.
}
\]

`negative_cost_le_full` proves the genuine uniform improvement
`C_N^- <= sqrt(E_N P_N)` for the **same** original weights and profile.
The floor therefore does not require an upper bound or decay of the
entire signed source. The earlier full energy bound remains a consequence.

There is no owner-column adjacent-variation allowance in this inequality,
no density approximation, and no assumed Type-II or large-sieve estimate.
The remaining one-sided cost is an explicit quantity with the actual
funding still correlated with the original remainder. No estimate that it is
eventually `<=79/1000+o(1)` has been proved. The earlier bounds remain
available; this energy is not claimed uniformly smaller than costs using
different owner coordinates or different profiles.

## The precise cross-population saving

For disjoint populations `S,T` under the **same** endpoint, profile and
weight, the checked identity is

\[
E(S\cup T)=E(S)+E(T)+2\sum_{k\text{ active}}
              \frac{\Phi_S(k)\Phi_T(k)}k.
\]

The cross term stays signed. Cauchy--Schwarz is used only after the full
signed correlations have been formed. Consequently the joint square-root
cost never exceeds the sum of separate costs under this same profile,
even for an arbitrary finite partition. No cardinality factor is needed.
The exact saved squared cost for two populations is

\[
2P\left(\sqrt{E(S)E(T)}
 -\sum_{k\text{ active}}\frac{\Phi_S(k)\Phi_T(k)}k\right).
\]

This measures actual cancellation or lack of coherence. It does not
assert negative cross terms or orthogonality from bin occupancy.

## What the many-bin condition does not prove

Occupancy counts locations, not weighted mass. It does not prevent a few
bins from carrying most of the weighted contribution. The earlier
`ZetaRieszManyBinPhaseAudit` also proves that the owner shift compensates
the cofactor log in the phase and that within-label bin deletions reproduce
the same full response. Thus the bins are not independent frequencies.

Even an exponential discount per available bin is only polynomial in `N`
because the number of bins is logarithmic. The earlier positive-envelope
no-go remains valid. None of these observations rules out cancellation
between different actual labels; the new energy retains precisely those
cross-label and cross-count correlations, together with the funding.

## Optional actual-integer regression

`scripts/probe_riesz_rejoined_phase.py` computes actual squarefree labels,
Möbius divisor signs, factorial weights and full fixed-height phases for
orders `4,5,6`, at heights `0,54,65,100`. It joins all sampled counts before
computing the energy, and checks the signed bound and cross-term identity.
The common profile endpoint is the largest selected original label.

The test length is `11N/8`, **not** the repository's rounded moving length.
The allocation is exactly zero at these orders: the necessary integer
conditions of `unpaidOrders_support` have no solution. These finite tests
are **not** the growing unpaid count-56-plus population, and their
factor/owner restrictions are not the full literal core mask. The probe
is floating-point exploration, not interval certification or a floor
certificate. It is optional and outside ordinary builds and CI.

All twelve tests pass. In the nine tests at heights at least `54`, the
joint two-sided cost is `45.9%..71.3%` of the separate-count cost; the new
one-sided cost is `26.0%..68.4%` of that joint two-sided cost. Those are
finite **cost comparisons**, not percentages of the unresolved floor
gap. The full signed prefix pairing is checked independently against the
actual divisor-sum carrier. No asymptotic rate or saving on the growing
unpaid population is certified by these low-count examples.

The quantitative open question is now whether the **actual combined**
adverse-prefix cost above is small enough at source scale. Merely
substituting the many-bin count for such an arithmetic estimate would not
close the floor. No ceiling, restricted contradiction or new zero
exclusion is asserted.
