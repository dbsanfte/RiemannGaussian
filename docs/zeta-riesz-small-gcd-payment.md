# A wider actual shared-factor payment in the whole floor

The independent `-79/1000` floor remains **open**. This slice independently
pays more of the **existing** whole signed pair energy across every retained
count, share geometry and radial period. It does not introduce another
physical carrier or assume that phases cancel.

Proof: [ZetaRieszSmallGcdPayment.lean](../RiemannGaussian/ZetaRieszSmallGcdPayment.lean).
Validation: [focused proof audit](riesz-small-gcd-payment-audit.json).

## Use the actual inverse-square common-factor decay

The preceding payment used

\[
\log\gcd(n,m)>N/1000
\]

and charged the common-factor inverse square using a one-half tail
exponent. The remaining half was kept in a convergent divisor mass at
`3/2`. The same exact squarefree common-factor convolution instead permits
the exponent `99/100`, retaining a convergent divisor mass at `101/100`.

For the new threshold `log(gcd(n,m))>N/4096`, the actual pair mass is bounded
by

\[
\left[e^{\log X/262144}M(1+1/262144)\right]^2
e^{-99N/409600}M(101/100),
\]

where `M` is the already-defined `divisorSquareDirichletMass`. These fixed
masses are finite values of convergent nonnegative divisor-square
Dirichlet series. Their numerical values are **not evaluated** here.

Squarefreeness preserves the exact divided labels and the multiplicative
divisor cardinalities. No prime-density or short-interval estimate enters.

## The source growth is included in the saving

For `0<u<=10001/20000`, the checked bound `log(2u)<=1/10000` gives

\[
2\log(2u)+\frac6{262144}-\frac{99}{409600}
\le-\frac1{65536}.
\]

Lean proves the corresponding power/exponential inequality even at
`u=0`, without taking its logarithm. For actual normalized prime weights,
allocation and funding bounded by `B`, it follows that

\[
|E_{\mathrm{shared}}|
\le C(B)(N+1)^3e^{-N/65536},
\]

\[
C(B)=16U^2B^2M(1+1/262144)^2M(101/100)e^{6/262144},
\qquad U=10001/20000.
\]

The associated floor price is bounded by

\[
\sqrt{4C(B)}(N+1)^2e^{-N/131072}\longrightarrow0.
\]

The estimate holds for **any pair-selection mask**, including masks
depending on the original phases or joined Gram. It is proved by bounding
the selected sum itself; it does not infer a bound for a subfamily from
the norm of a potentially cancelling larger sum.

The new lower threshold is `4.096` times smaller in logarithmic units.
The decay is slower and the fixed constants are larger. This measures a
geometric threshold change, not a percentage of energy, carrier mass or
the floor deficit. No effective starting order is certified.

## Exact disjoint placement in the current ledger

The added pair selection is the **original** `retainedPair`, so the new
payment covers only

\[
N/4096<\log\gcd(n,m)\le N/1000
\]

outside the already paid near-label and phase-orbit families. It is
disjoint from all earlier paid pair families. `paidPair_band` records
the exact old/new common-factor interval.

The adverse cutoff set is selected **once** on the entire original
count-cropped core. `maskedSharedEnergy_eq_gram` keeps that identical
cutoff Gram, and `nonOrbitEnergy_eq` proves the exact partition

\[
E_{\mathrm{old}}
=E_{\mathrm{additional\ shared}}+E_{\mathrm{remaining}}.
\]

The remaining term keeps every sign, allocation and phase before its
whole cost is taken. It is not reselected by count, owner, period or
pair sign. Removing a negative family can increase the finite remaining
cost; no monotonic decrease in the exact energy is asserted.

`eventually_joined_floor` applies this directly to the **original**
`joinedPhysical` at the **original** `dyadicPrimeCount`. The main energy
uses the previously checked `K/864+1` count endpoint with natural division.
One original core/joined bridge, the four old pair prices, the original
count-tail payment and the added shared-factor price occur **once**.
No auxiliary supply/debit or favorable count credit is spent.

## Exact remaining arithmetic target

The still-unpaid main pairs satisfy

\[
\log\gcd(n,m)\le N/4096,
\]

and retain the previous near-label and phase-orbit exclusions. The labels
still have all original core, count, physical, nondominant, factorial
allocation, moving length and complex phase conditions.

The whole-floor comparison is now

\[
\Re[u^{N+1}\mathrm{joinedPhysical}]
\ge-\sqrt{\frac{129N}{200}\max(E_{\mathrm{remaining}},0)}-e_j,
\qquad e_j\to0.
\]

The independent sufficient budget

\[
E_{\mathrm{remaining}}\le\frac3{320(N+1)}
\]

is **unproved**. Coprime and smaller shared-factor correlations can still
reinforce; phase separation does not imply automatic orthogonality. This
slice pays an actual global correlation family but certifies no numerical
floor margin, multiplicity ceiling or zero exclusion.

Twelve public proofs pass focused Lean/root/lint/standard-axiom checks.
All earlier mathematical sources, staged semiprime files, README and
published explorer endpoints remain unchanged. Work is local without
commits, pushes, subagents or wider publication gates.
