# Spending the signed small-tag rows on the native floor

Local work after `194a361762f404a8f4473298b25d96fbae0bb56e`.
The whole floor **−399/5000**, ceiling **42/25**, restricted contradiction
and RH remain open. This slice changes no public endpoint.

The checked module is
[ZetaRieszSmallTagNativeFloor](../RiemannGaussian/ZetaRieszSmallTagNativeFloor.lean).
It applies the previous independent complete-row cancellation theorem
to a concrete population of the actual native carrier. It then removes
that population before the remaining cutoff-period debits are clipped.

## Exactly which labels are now paid

Use the original dyadic moment/count schedule, physical prime set,
moving Riesz length and core window. Select `n=p*a`, where:

- `p` is an original intermediate prime, with
  `51N/50 <= log p <= 5N/4`;
- `39N/20 < log(p*a) <= 203N/100`;
- `a` is squarefree and composite;
- the least cofactor prime lies in `(N^2,N^3]`;
- the actual native prime-count ceiling is retained.

The canonical least-tag exclusion set forbids only primes smaller than
the tag. Every larger cofactor prime remains allowed, including any
number of further primes below `N^3`. This is not an exactly-one-small-
prime population.

The complete-window geometry proves `a<p`, hence `p` is the unique
largest prime. `rows_injective` prevents duplicate product labels.
`eventually_labels_subset_native` proves these labels satisfy the
original native masks. In particular, every prime log is below
`(13/20)*log n`, so neither the old dominant sector nor the old
cancellation sector removes an interior piece of the row. The count
crop is the actual `dyadicPrimeCount(j)/864+1`, not a replacement ceiling.

## Comparison premises are proved, not assumed

For every selected owner, choose the same explicit integer cutoff

\[
R_N=\lfloor e^{N/2}\rfloor.
\]

The lower cofactor endpoint is exactly

\[
M_p=\lfloor e^{39N/20-\log p}\rfloor.
\]

`coreFloor_lower` proves `M_p >= exp(2N/3)` for `N>=64`. Thus
`0<R_N<=M_p` and `R_N^4<=M_p^3`. The actual length satisfies
`5N/4 <= L_N <= 139N/100` eventually. The owner lower bound gives

\[
L_N-\log p\le \frac{37}{100}N\le\log(R_N+1).
\]

`eventually_cube_below_core` also proves `N^3<=M_p` uniformly over
the selected owners. All premises of the prior signed comparison
therefore follow from the actual native parameters.

## Independent signed estimate, including the full allocation

Let `D_j=labels u j` be this disjoint population and let `A_N` be the
original intermediate primes. The real packet is exactly

\[
P_j=\operatorname{Re}\left[
u^{N_j+1}\sum_{n\in D_j}
\operatorname{residualCoefficient}(A_{N_j},L_{N_j},N_j,n)
K_{N_j}(3/2+i y,n)\right].
\]

For fixed `|y|>=54` and `1/2<u<=10001/20000`, the checked result is

\[
|P_j|\le E_j\quad\text{eventually},\qquad E_j\longrightarrow0.
\]

These are `eventually_packet_bound`, `budget_tendsto` and
`tendsto_packet`. There is no hypothetical-zero, exposed-source,
rightmost-zero or unproved arithmetic cancellation premise.

The explicit budget is the previous `selectedNativeBudget` plus the
existing global nonowner bound restricted once to these labels:

\[
E_j=\operatorname{selectedNativeBudget}(u,y,j)
 +\frac{4(N_j+1)}3\,r^{N_j}
 \frac{1509}{1000}\operatorname{zetaMoebiusLogMajorantMass}(2049/2048),
\qquad 0\le r<124/125.
\]

The count allowance is already included in `selectedNativeBudget`.
The count and nonowner errors are each used once. This is a **real
signed** estimate, not a claim of complex norm decay or small absolute
cutoff variation.

## The whole floor now spends this payment

Keep all logarithmic complex null coefficients and the whole tangent
correction. This alternative uses **zero imaginary tilt**, because the
independent row estimate controls the real signed total. The old tilted
price remains available as a separate alternative.

`paidIncrement` uses the same native cutoff profile and logarithmic
null coefficients. `eventually_sum_paidIncrement` proves that its
signed total is precisely `P_j`. `eventually_step_sub_paid` proves
that subtracting it leaves the null-corrected main response on
`nativeLabels.filter Squarefree \ D_j`; the whole free tangent
correction remains joined. No absolute cutoff variation of `D_j`
is charged.

Define the explicit remaining price

\[
D_j^{\rm cost}=\operatorname{blockCost}
 \bigl(\operatorname{step}_j-\operatorname{paidIncrement}_j\bigr)
\]

on **every original cutoff**, including early and boundary groups.
The checked whole-carrier inequality is

\[
\operatorname{Re}\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
\ge -D_j^{\rm cost}-E_j-\operatorname{nativeError}_j
\quad\text{eventually}.
\]

This is `eventually_joined_floor_pruned`. No count, phase, remaining
share geometry or cutoff period is separated before pricing.

Deletion need not improve every particular clipped period. Accordingly
the new `price` is the minimum of the previously valid
`nativePrunedPrice` and `D_j^{cost}+E_j`. `eventually_joined_floor`
proves the same whole-floor inequality using this minimum, and
`price_le_previous` proves it cannot worsen the old available price.
The exact additional `gain` is nonnegative; it may be zero. No positive
fraction of the global floor deficit is certified.

## What remains open

`false_of_cofinal_price` retains the explicit, **unproved** premise

\[
\operatorname{price}_j\le399/5000\quad\text{cofinally}.
\]

The independent payment above does not supply this whole-cost bound.
Fully `N^3`-rough cofactors have no retained tag. Their ordinary-prime
cofactor subtraction must remain signed and joined. Owner windows not
covered by `51N/50..5N/4`, especially partial windows and geometries
with the whole cofactor larger than its owner, are also unpaid by this
theorem. Previous negative audits and the divergent `restAllowance`
remain in force.

Scoped strict Lean, targeted leaf build, compiled ordinary-root plus
leaf namespace lint and transitive axiom audits are recorded in
`docs/riesz-small-tag-native-floor-audit.json`. No root-source rebuild,
wider publication gates, subagents, commit or push are part of this slice.
