# Wider global phase-period payment

The floor is still open. `ZetaRieszWidePhasePayment` pays one additional
explicit family of the **actual** remaining cross correlations, with every
original count, owner, allocation, physical, radial and phase mask retained.

The preceding phase payment used log width
`exp(-N/1000)/(1+abs(y))`. The new width is
`exp(-N/4500)/(1+abs(y))`, around **every** total-log phase period in the
original finite label range. The extra family is restricted to the old
remaining pair mask, including `log(gcd(n,m)) <= N/4096`. It is disjoint
from the already paid phase, near-label, common-factor and diagonal families.
Both energies use the adverse cutoff set selected once on the original
whole population. No count-specific or pair-specific reselection occurs.

For an arbitrary additional pair mask and the actual weights
`w(n)=u^(N+1)*q(n)*primeWeight(A,L,y,N,n,1)`, with `abs(q)<=B`,
`L>=1`, `0<=u<=10001/20000`, fixed `abs(y)>=3`, and the existing literal
label/log windows, Lean proves

```math
|E_{\rm wide,masked}|
\le C(B,y)(N+1)^4 e^{-N/100000}.
```

Here `C(B,y)=80 U^2 B^2 phaseCount(y) M(1+1/262144) exp(3/262144)`,
`U=10001/20000`, and `M` is the existing convergent divisor-square
Dirichlet mass. Its value and an effective arithmetic starting order are
**not** evaluated. Its square-root price is
`sqrt(4C)*(N+1)^3*exp(-N/200000) -> 0`.

The proof uses reciprocal neighbour capacity on actual integer labels.
It does not compare a signed sum with a larger cancelling sum, approximate
prime density, or infer orthogonality from coprimality or bin occupancy.
Only the sparse family is norm-paid. The exact rational exponent audit is

```math
2\log(2U)+\frac3{262144}-\frac1{4500}
\le -\frac{15893}{1474560000} < -\frac1{100000}.
```

The native `eventually_joined_floor` theorem connects this payment to the
**original** `joinedPhysical`, original dyadic schedule and previously
proved count crop. Its remaining cost is
`sqrt(max(wideRemainingEnergy,0)*(129N/200))`; its errors tend to zero.
The numerical budget for that signed remainder is still unproved.

This widening is a new independent geometric payment, not a claim that
the signed remainder decreases monotonically. Removing a negative paid
piece can increase the remainder; the exact norm price accounts for
either sign. Nor does the wider logarithmic interval give a percentage
of carrier mass, energy, or floor deficit removed.

The optional `scripts/probe_riesz_wide_phase_payment.py` enumerates complete
subsets of constructed probable-prime universes at native small orders,
keeps their original masks and weights, and verifies the old/new signed
partition at a single whole-population adverse selection. These use
common amplitude rescaling and log interpolation. They are not full-core,
interval, primality, eventual-order or source-budget certificates; the
eventual count crop is not applied at these small orders. This script is
outside ordinary builds and CI.

In twelve native-small-order tests (N=256/640, two seeds, heights54/65/100),
the new band contains1858..6830 ordered pairs of these constructed subsets.
Its signed contribution is positive in six cases and negative in six.
The signed remainder therefore increases in six cases on removing it.
This is consistent with the exact norm payment; it does not establish
energy monotonicity or any full-core mass/deficit percentage.

A literature check of Ramaré–Zuniga-Alterman's
[Möbius double-sum paper](https://arxiv.org/abs/2603.25961) found bounds for
the complete inverse-lcm sieve quadratic form. Their stated theorem does
not supply a bound for our hard-masked phase-weighted cutoff Gram. No such
transport or literature assumption is used in this payment.

Twelve public proofs pass focused warnings-as-errors direct/targeted Lean,
ordinary root import, all 14 namespace linters and transitive standard-axiom
checks. See `docs/riesz-wide-phase-payment-audit.json`. All prior Lean
modules, the staged semiprime files, README and published explorer endpoints
are preserved. No commit, push, zero exclusion or RH result is claimed.
