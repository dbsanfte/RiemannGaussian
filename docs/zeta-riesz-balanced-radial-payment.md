# The balanced main is restricted to the contracted radial core

`ZetaRieszBalancedRadialPayment` spends the **existing** uniform radial
estimate in `ZetaRieszLargeOrderCore` on the current allocation-free balanced
sum. It does not claim a new generic radial estimate or a bound on the
surviving signed main. The whole floor remains open.

The original remainder has `log(largestPrime n)<51N/50` and all native
squarefree, count, physical and nondominant masks. Its original coefficient
and full complex phase are unchanged. Both outer strips are now removed
before pricing the complete cutoff periods:

```text
centralLabels = restLabels intersect {1.971N < log n <= 2.029N},

||centralRest - unallocatedRest|| <= C * exp(-N/1000000),

C >= 0 is the SAME finite constant from the proved all-mask radial bound.
```

`central_sub_unallocated_norm_bound` holds for arbitrary real phase height
and `0<=u<=10001/20000`, without a zero or exposure hypothesis. The estimate
pays only the difference. It never norm-pays the central main or the prime
correction. No small finite-order value of `C` is asserted.

`central_owner_share_lt` and `central_prime_log_lt` strengthen the exact
geometry of every remaining label to

```text
log(largestPrime n)/log n < 340/657,
log p < (340/657) log n for EVERY prime factor p.
```

This is about 0.5175, compared with the earlier owner cap 34/65. The radial
window is narrower, but its width is not a percentage of the unresolved
floor deficit or a numerical source-mass saving.

The SAME full signed `nativeHead` stays in the ledger. In particular its
radial support is not contracted along with the balanced sum.
`tendsto_central_sub_head_sub_native` proves that

```text
Re(centralRest_j) - nativeHead(N_j)
  = Re(source-scaled native core_j) + o(1).
```

`sum_step` identifies the literal total of the contracted increment.
`eventually_joined_floor_paid` spends the radial payment once, alongside the
previous high-owner and allocation budgets and the unchanged `nativeError`.
All counts, crossings, periods and the original whole-native tangent/null
columns are assembled before clipping. `price` keeps the earlier funded
whole price as an alternative: deleting signed labels is not assumed to
reduce clipped cost. No overlapping credits are stacked.

The optional `scripts/probe_riesz_balanced_joint.py` exhausts squarefree
integer labels/divisors on six small **toy** examples, keeping phases, all
available counts and the same signed head together. Its length is
`-2N log u`, not the repository's moving integer length; orders 6 and 7 are
not the native dyadic schedule, and the native deletion masks are not all
imposed. Thus its tiny finite costs cannot certify the actual eventual
floor. No existing eventual native budget is applied to these toy orders.

The baseline runs verify cancellation across counts and the head, with the
same null coefficients on all components. The `--compare-radial` runs price
the contraction with the **actual finite signed removed total**, rather than
assuming the eventual geometric budget is already small. All six such
funded comparisons choose the older full price; none improves the finite
price after the removed total is charged. This negative finite diagnostic
does not contradict the proved asymptotic payment. Earlier baseline output
and source snapshots are preserved, and rerun baseline totals agree.

Extending the old owner-window phase estimate down to the square-root
ownership boundary is not licensed by this slice. That extension introduces
an interior endpoint near `log n=2N`; the old estimate explicitly requires
the two original exterior total-log endpoints. No geometric payment for
that new endpoint is assumed.

The remaining arithmetic theorem is still a cofinal signed floor for the
contracted balanced main minus the same head, strong enough for the funded
whole price `<=399/5000`. The central main bound, ceiling `42/25`, restricted
contradiction, zero exclusion and RH remain open. Validation is local:
strict leaf, targeted leaf build, frozen compiled ordinary root plus explicit
leaf lint and all-declaration transitive standard-axiom audit. No wider
gates, root registration, public endpoints, commits or pushes are included.
