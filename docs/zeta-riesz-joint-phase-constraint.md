# The joint floor needs the actual logarithmic prime correlations

The new local leaf `ZetaRieszJointPhaseConstraint` tests whether the existing
divisor geometry, all-count signs and original weights alone can force
cancellation of the central main with the same prime head. It establishes
a precise limitation of estimates valid for arbitrary multiplicative prime
signs. It does **not** refute cancellation at one actual fixed height.

Every native `centralLabels` label has at least one prime outside the
entire head support. A head owner has logarithm at least `1.02N` and cannot
divide a central label whose largest-prime logarithm is below `1.02N`.
Every head cofactor prime has logarithm greater than `0.7N`. If all three
or more prime factors of a central label were such cofactors, its total
logarithm would exceed `2.1N`, contradicting the exact upper endpoint
`2.029N`. This uses the squarefree logarithm identity and retains every
native count and physical mask.

Fix all head-prime signs at one, and vary the signs on the remaining finite
prime pool `F`. For `V` contained in `F`, put

```text
chi_V(n) = product over p|n of (-1 if p in V else 1).
```

These are multiplicative signs with the same value on every occurrence of
a prime. They are not independently assigned label phases. Since every
central label contains a free prime, its exact full sign-cube average is
zero. Summing **all** original signed central amplitudes preserves zero.
Both prime legs of every original head pair keep sign one, so its sieve,
allocation, factorial kernel and support remain unchanged.

Consequently `exists_joint_le_neg_head` proves that some such sign choice
has the joined value at most `-nativeHead u 0 N`. The generic theorem
`arbitrary_sign_allowance_ge_head` makes the pricing consequence explicit:
any lower bound justified for every such sign choice must charge at least
the whole height-zero head. This is an exact signed inequality, without
prime-density approximation, completion, termwise norms or count prices.

The optional probe evaluates the original toy windows at orders 6, 7 and
8. It fixes the full candidate head support, including prime pairs with
zero sieve weight. All 18 independently reevaluated complex totals at
heights 54, 65 and 100 match the frozen data. A conditional-expectation
walk constructs adverse sign choices while preserving shared prime
incidences. These are floating diagnostics, not numerical certificates.
The earlier smaller weighted-support experiment is also preserved.

The chosen signs are **not** asserted to equal `exp(-iy log p)` for one
fixed ordinate. No native height-zero head growth theorem is proved here,
and no eventual counterexample to the fixed-height floor follows. The
toy orders, length and deletion masks are not native; no eventual budget
is applied to them.

This pass supplies no new arithmetic floor saving. It narrows the required
input: the whole signed first-harmonic estimate must exploit the actual
logarithmic prime correlations. The independent floor `-399/5000-o(1)`,
ceiling `42/25`, restricted contradiction and RH remain open. Validation
is the strict leaf, targeted build, frozen compiled ordinary root with
explicit-leaf lint and standard-axiom audit. Everything stays local.
