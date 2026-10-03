# Shared-prime cancellation in the balanced main/head comparison

The local goal remains **Close out the floor**. The independent cofinal
floor `-399/5000-o(1)`, ceiling `42/25`, restricted contradiction and RH
remain open. This slice applies the existing Riesz saturation mechanism
to the exact intersection of the unpaid main and the signed prime head;
it does not claim a new zero-free region or a numerical floor margin.

## Checked cancellation on the native masks

[`ZetaRieszHeadSharedCancellation`](../RiemannGaussian/ZetaRieszHeadSharedCancellation.lean)
uses the same central native labels and the **same full** head intervals.
It applies for `1/2 <= u <= 10001/20000` and native order `N >= 65536`,
without an exposed-zero, multiplicity, height or phase hypothesis.

Every genuine prime `q` from a head cofactor interval satisfies
`log q > 7N/10`, including the exact integer lower endpoint. If it is a
nonowner factor of a central main label, its largest prime `p` also has
`log p > 7N/10`. The native moving-length bounds give

```text
log n <= 2029N/1000,
277N/200 <= L <= 139N/100.
```

Both deletion cutoffs are saturated because
`log(n/p), log(n/q) < 1329N/1000 < L`, while
`L-log p-log q < 0`. The exact two-prime insertion identity, on the
remaining squarefree cofactor `a=n/(pq)`, therefore gives

```text
R_L(pqa) = Lambda(a) - Lambda(a) - Lambda(a) + 0 = -Lambda(a).
```

For total count at least four, `a` has at least two distinct prime
factors, so `Lambda(a)=0`. This is an exact zero of the **original**
coefficient, not a bound on a surrogate or a parity convention.

`central_nonowner_head_zero` proves this on the original labels.
`higher_count_profile_eq_owner` then joins all shared-prime incidences
before taking a real part or norm:

```text
sum_n sum_{q | n, q in headSupport} c(q) * coefficient(n) * w(n)
  = sum_n 1_{largestPrime(n) in headSupport}
      * c(largestPrime(n)) * coefficient(n) * w(n),
```

where `n` runs over every central label of count at least four. `c` and
`w` are arbitrary complex weights; the actual factorial kernel, source
scale, allocation and product phase may be retained in them. No count
multiplicity or completion error survives in this shared profile.

`nonownerShared_sum_eq_zero` pays the entire corresponding literal
subpopulation exactly. `nonownerShared_source_floor` gives its independent
floor zero, and `centralRest_eq_without_nonownerShared` removes it from
the current main with exact equality. The same full signed head is kept.
The triple exception remains: its cofactor can be prime and its coefficient
can be nonzero. Labels without a shared head prime and the surviving
higher-count owner profile are not paid by this theorem.

This specializes a previously available saturation mechanism. The
new reduction is its use on the whole main/head shared-incidence profile;
it is not an additional payment of labels already treated as exact zeros.

## Whole signed numerical audit

[`probe_riesz_joint_interference.py`](../scripts/probe_riesz_joint_interference.py)
evaluates every count and the same full complex head on the frozen toy
population. It tests 180 points: orders 6/7/8, 30 actual logarithmic phase
heights, and both the old and narrowed windows. All 18 frozen complex-total
regressions pass. The response cutoff is checked with integers; logarithms,
phases, factorial weights and sums use floating arithmetic.

The finite audit checks the exact shared-profile decomposition into the
owner contribution and the nonowner triple exception. It detects 749
cancelled full-window labels at order 7 and 29,778 at order 8 (642 and
24,605 in the narrowed window). Their integer response signatures are
identically zero. These counts are finite diagnostics, not percentages
of the native floor deficit or new credits against earlier budgets.

Count cross terms are negative **within the least-prime grouping** at
all 180 tested points. The global count cross terms reinforce at 13 of
those points. For example, at order 6 and height 90 in the narrowed
window, the joint squared magnitude is about 2.224 times the separated
count diagonal energy. Shared owner/head incidence cross terms also
have both signs. A common prime or favorable local interference is
therefore not sufficient to assume a global orthogonality saving.

A separate 28-point stress test at heights up to 10,000 also finds
**positive** within-least-prime cross terms at 11 points (for example,
order 6 and height 500). Its four frozen complex-total regressions pass.
The negative local sign in the first scan is consequently not a universal
finite-height law. This does not disprove an eventual native estimate;
it rules out treating the observed finite pattern as one without proof.

The main and head have disjoint least-prime supports in this probe.
Cross-least-prime correlations and the signed head remain explicitly in
the energy ledger; incidence energy is **not** the whole-carrier energy.
There is no phase rotation, independent-incidence assumption, separate
count allowance or source-scale certificate.

The toy length is `-2N log u`, not the native damped integer length,
native dyadic schedule or all deletion masks. No eventual native budget
is used at these small orders. The probe is optional and outside CI/builds.

## Remaining estimate

The shared higher-count comparison now has a unique owner per nonzero
label. Its signed owner profile must still be bounded jointly with the
full correction; the triple exception and nonshared main population also
remain. The height stress test prevents assuming a universal negative
within-least-prime correlation. No cofinal cancellation rate is proved.

Validation is local: strict leaf, targeted build, frozen compiled ordinary
root plus explicit-leaf namespace lint and standard-axiom audit of every
compiled declaration. See `riesz-head-shared-cancellation-audit.json` for
the frozen evidence. No root registration, public endpoint update, commit,
push, subagent or wider gate is performed.
