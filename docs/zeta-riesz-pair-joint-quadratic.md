# Join the Selberg trace and pay the whole square correction

The entire repeated-prime correction now has an independent geometric
source-scale bound. It is spent once in the original whole-core floor.
The retained signed central quadratic remains unpaid: the independent
cofinal target is still `Re prefixPairDefect <=399/5000+o(1)`. No new floor,
multiple-zero ceiling, zero exclusion or RH proof follows from this slice.

The local leaf is
[`ZetaRieszPairJointQuadratic.lean`](../RiemannGaussian/ZetaRieszPairJointQuadratic.lean).
It retains the complete finite prime universe licensed by the preceding
whole symmetric completion theorem, and keeps all complex prime phases.
No prime-square label is added to the literal carrier.

## Exact joint bookkeeping

Write `M=N+1`, `K=floor(13N/32)`, and

```math
P_k=\sum_{p\in A}K_k(s,p),\qquad
H_k=\sum_{p\in A}(\log p)K_k(s,p)=(k+1)P_{k+1}.
```

`selberg_pairs_eq_trace` proves, for `N>0`,

```math
\sum_{p<q\in A}\mathrm{Selberg}(pq)K_N(s,pq)
=-\frac1N\sum_{k=0}^{N-1}H_kH_{N-1-k}
  +\frac12\sum_{p\in A}(\log p)K_N(s,p^2).
```

The ordinary-prime term cancels exactly. The trace keeps both incidences
and every endpoint, and the full square correction is accounted for once.
`selbergTrace_eq_weighted_orders` expands each logged slot before
collection:

```math
\sum_{k=0}^{N-1}H_kH_{N-1-k}
=\sum_{k=0}^{N-1}(k+1)(N-k)P_{k+1}P_{N-k}.
```

`selbergTrace_order_weight_pos` proves that every scalar weight after
division by `N` is positive. Thus the Selberg subtraction reinforces the
same order-`M` monomials as the unlogged central band. This is a statement
about scalar coefficients, not the sign of their complex real parts.
It supplies no new endpoint cancellation or permission to norm that band.

Define the single coupled quadratic, using exactly the previous central
order sets,

```math
\begin{aligned}
\mathcal Q_{N,A}
={}&\frac M2\sum_{K<k<M-K}P_kP_{M-k}
-\frac{M(M+1)}{2L_N}\sum_{K<k<M+1-K}P_kP_{M+1-k}\\
&-\frac M{L_N}\sum_{k=1}^{K}kP_kP_{M+1-k}
+\frac1N\sum_{k=0}^{N-1}H_kH_{N-1-k}.
\end{aligned}
```

Let `f_N=lowerMass(M,K,1/2)` and
`S_N= sum_(p in A) log(p) K_N(s,p^2)`. The previously separate prefix
diagonal and Selberg diagonal combine exactly into

```math
\mathcal D_{N,A}
=\left(2f_N-\frac32\right)S_N
+\frac M{L_N}(1-f_N)S_{N+1}.
```

`finitePrefix_eq_quadratic_add_square` proves

```math
\mathrm{finitePrefixPairDefect}_{N,A}
=u^{N+1}\left(\mathcal Q_{N,A}+\mathcal D_{N,A}\right).
```

There is no isolated count allowance, share-mask approximation, removed
order-zero contribution, or dropped repeated-prime term in this identity.

## Independent quantitative saving

For `N>=65536`, `1/2<=u<=10001/20000`, every real height and every finite
ordinary-prime universe, `norm_normalized_joinedSquare_le` gives

```math
\left\|u^{N+1}\mathcal D_{N,A}\right\|
\le\frac{17}{6}\,u\,\mathsf{SquareMass}
       \left(\frac{4u}{3}\right)^N,
\qquad
\mathsf{SquareMass}
=\sum_{n\ge0}\frac{\log n}{n^{3/2}}
```

with the repository's totalized exponential/log convention at `n=0`.
This finite mass is proved summable; it is a majorant over all integers,
not just primes. `squareBudget_le_uniform` bounds the geometric rate by
the exact rational `10001/15000`. There is no exposed-zero assumption,
height restriction or numerically estimated constant in this payment.

`eventually_norm_prefix_sub_quadratic_le` adds the independently paid
whole-completion difference, without estimating the signed quadratic.
`eventually_native_quadratic_floor` spends the Selberg, owner, whole
completion and joined square budgets exactly once in the original native
whole-core floor. `exists_native_quadratic_payment_simple` proves these
four budgets vanish under the original simple exposed-zero hypotheses.
It does **not** prove the independent `399/5000` bound on the quadratic.

The earlier physical low-order payment keeps its original masks and
population. It is neither spent again nor extended to the completed
population by this identity.

## Optional detector and delayed-source null test

[`probe_riesz_pair_joint_quadratic.py`](../scripts/probe_riesz_pair_joint_quadratic.py)
now retains the unjoined Selberg factorial slots, orientations and common
phase/support signatures as well as the original prefix components.
It checks 202 exact rational coefficient cases through native order 8192,
including the repeated-prime diagonal, before evaluating primes. Wrong
Selberg signs and differing masks are rejected.

There are 36 high-precision finite genuine-prime phase regressions. These
use a generic positive length `7*(N+1)/5`, not the literal moving length,
and orders at most 64, below the formal 65536 threshold. They validate the
exact identity and square payment only; they are not the exhaustive
literal prime population and receive no cofinal floor credit.
[`check_riesz_pair_joint_quadratic.py`](../scripts/check_riesz_pair_joint_quadratic.py)
independently checks every order in the rational cases and replays prime
phases, factorial recurrences, binomial prefixes and the single diagonal
without importing the producer.

The synthetic selected-mode null test uses `k*u^k*P_k=-1`, `k>=1`, and the
literal moving length. At the radius ceiling its joined quadratic is
approximately `0.0796113` at `N=90112`, then `0.0798099` at `N=425984`, and
approaches `0.079871797...`. Hence passing the `0.0798` target at finite
orders does not imply a cofinal bound. This is a model of the retained
hypothetical source, not an arithmetic counterexample or observed residual.
The difference `0.000071797...` remains a contradiction margin.

The probes stay outside ordinary builds/CI. Work remains local, with no
root registration, broader gate, commit or push. The focused Lean build,
namespace lint, full leaf axiom audit and independent replay are pinned in
[`riesz-pair-joint-quadratic-audit.json`](riesz-pair-joint-quadratic-audit.json).

The next required mathematics is an independent signed upper bound for
the **whole** coupled quadratic, exploiting the actual ordinary-prime
moments across its positive and negative order bands. Coefficient
bookkeeping, exposure, finite-order examples and the new square payment
do not establish that inequality.
