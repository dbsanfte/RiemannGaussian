# A global semiprime/head cancellation in the native floor

Local research, 2026-10-03. The goal remains **Close out the floor**.
The cofinal floor `-399/5000`, ceiling `42/25`, restricted contradiction
and RH remain open. This slice proves a whole-population cancellation
inequality and pays the mismatch between its two literal radial masks.

[`ZetaRieszGlobalHeadCentralPayment`](../RiemannGaussian/ZetaRieszGlobalHeadCentralPayment.lean)
keeps the same original head, physical owner cutoff, ordinary-prime sieve,
moving integer length, full factorial allocation and complex product phase.
There is no exposed-zero hypothesis or complete-prime phase transfer.

## The radial mismatch is funded

The head originally spans `1.95N < log(pq) <= 2.03N`, while the completed
semiprime boundary spans `1.971N < log(pq) <= 2.029N`. They cannot be
identified without paying this difference.

The new proof moves the head pairs onto their exact product-label axis.
`pair_cofactor_lt_owner` makes the larger prime the canonical largest
prime, so the map `(p,q) -> pq` is injective. Nonprime cofactor slots
were already zero. No nonzero head atom or allocation order is deleted.

On every original head label, the existing exact response domination
gives a nonnegative head coefficient bounded by the negative of the
original semiprime completion coefficient. Its norm therefore obeys
the same divisor-log majorant. Applying the proved all-mask radial
estimate to this coefficient yields, for
`1/2 <= u <= 10001/20000` and `N >= 65536`,

```text
norm(fullHead - centralHead) <= E_N,
E_N = radialConstant * exp(-N/1000000).
```

This is uniform in height, without a zero hypothesis. The finite constant
is inherited exactly; it is neither evaluated nor set to one. Only the
outer radial difference is paid. The signed full head is not small.

## Join the matching coefficients first

Every central head label is a genuine central squarefree semiprime.
On each matching label, the semiprime coefficient is nonpositive, the
head coefficient is nonnegative, and their sum is still nonpositive.
Their product phase is identical. Consequently the exact atom identity is

```text
norm(semiprimeAtom + headAtom)
  = norm(semiprimeAtom) - norm(headAtom).
```

Let `P2_N` include **every** central squarefree semiprime, including those
outside the head population. Write `D2_N` for its atom norm sum and `H0_N`
for the same full head at zero height. Zero height measures the matched
amplitude credit; the actual height and full phase are unchanged in the
joined carrier. The new global theorem proves

```text
norm(P2_N + fullHead_N(y)) <= D2_N - H0_N + 2*E_N.
```

The two error occurrences are different uses of the same funded radial
estimate: transfer the actual-height head, then transfer the zero-height
credit. Relative to the separated atom price `D2_N + H0_N`, the saving is
`2*H0_N - 2*E_N`. It covers the whole central semiprime population and the
same full head, rather than an auxiliary matched subset with unpaid masks.

This is a bound after same-label cancellation. It does not bound the
remaining prime or raw high-owner source by a positive allowance.

## Spend it in the whole native ledger

`prunedBoundary_upper` keeps the ordinary-prime and raw high-owner terms
as one signed scalar `V_N`. It gives

```text
prunedBoundary.re <= V_N.re + D2_N - H0_N + 2*E_N.
```

`eventually_native_floor_with_semiprime_credit` substitutes this into the
proved whole native floor transfer:

```text
nativeScaledCore.re
  >= -V_N.re - D2_N + H0_N - (nativePrunedBudget + 2*E_N).
```

All prior native payments are retained once. Raw high-owner coefficients
remain original and unallocated. The newly paid head strips are not
charged to the balanced main's already-paid radial difference. The full
head has not been spent a second time as an independent vanishing term.

The required independent bound is still for the **whole** remaining
signed boundary. Neither `D2_N - H0_N` nor `V_N` is proved cofinally small,
and the diagnostic atom price is not a new strategy for obtaining the
`399/5000` threshold. No numerical percentage of that deficit follows
from the exact head credit.

## Finite regression and validation

The optional
[`probe_riesz_global_head_central_payment.py`](../scripts/probe_riesz_global_head_central_payment.py)
joins the literal toy central semiprimes and original full head at orders
6, 7 and 8, heights 54, 65 and 100. All 18 frozen complex regressions pass.
Every matching product has one owner; every outer head atom retains its
signed phase. It checks the coupled atom price and exact head credit.

At order 8, it matches 103,835 central head labels and retains 24,955 outer
labels. The central head mass is about `0.001936`, giving an exact finite
central separated-price saving about `0.003871`. These are **toy** values,
not cofinal native margins or a zero-exclusion certificate. The probe uses
the frozen length `-2N log u`, not the native moving integer length,
dyadic schedule or deletion masks. No eventual estimate is applied at
these orders. It remains outside builds and CI.

Validation is focused: warning-as-error leaf, targeted build, frozen
compiled ordinary root plus explicit leaf, all 14 namespace linters and
transitive standard-axiom checks of every compiled declaration. See
[`riesz-global-head-central-payment-audit.json`](riesz-global-head-central-payment-audit.json).
No root registration, public endpoint update, commit, push, subagent or
wider gate is part of this local slice. All previous proofs and no-go
audits remain in force.
