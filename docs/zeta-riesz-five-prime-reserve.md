# Exact adverse five-prime debit in the joint floor

[`ZetaRieszFivePrimeReserve`](../RiemannGaussian/ZetaRieszFivePrimeReserve.lean)
evaluates the **positive part of every five-prime coefficient**. This is
the adverse arithmetic sign on negative-cosine observations, the same
phase sector where three-prime terms need compensation. The new theorem
sharpens the actual joint inequality without changing a carrier or mask.
The whole cofinal `-79/1000-o(1)` floor remains open.

## Exact formula and scope

For squarefree `n` with five prime factors, put `T=log n`, let `P` be its
largest prime and set `d=L-log P`. Define

\[
G_L(n)=2\log P+T-3L-
\sum_{q\mid n,\ q\ne P}(\log q-d)_+.
\]

If `L>0` and `2T/3<=L<=3T/4`, `positiveAllowance_eq` proves

\[
\boxed{(\Re c_L(n))_+=\frac{T}{L}(G_L(n))_+.}
\]

The defined `positiveAllowance` is zero on nonsquarefree labels, matching
their original coefficient. All actual small primes, endpoint equalities
and the moving length remain. The original core eventually supplies every
length hypothesis on `1/2<u<=10001/20000`.

`positiveAllowance_le_clipped` proves this exact debit never exceeds the
old minimum of the two largest-prime gaps and the three-least-log cap.
`five_floor_improves_clipped` transfers that comparison to every original
weighted observation on a nonpositive cosine. There is no phase average.

## Why the four-prime theorem applies

If `2 log P+T<=3L`, the existing five-prime sign theorem gives a nonpositive
coefficient and `G_L<=0`. Otherwise `P` lies above the reflected cutoff
`D=T-L`. Prime insertion after odd reflection gives exactly

\[
\Re c_L(n)=\frac{T}{L}R_D(n/P).
\]

If `log P>=L`, the cofactor response is saturated and zero; direct
evaluation gives `G_L=L-log P<=0`. In the remaining case the four-prime
cofactor satisfies the [exact clipped-balance theorem](zeta-riesz-four-prime-reserve.md).
Its reflected cutoff is `log(n/P)-D=L-log P`, so all cofactor-prime excesses
give precisely `G_L`. No cofactor is completed and no subset sign is lost.

## The original joint inequality

For `x=cos(y*T)<=0`, the original residual atom obeys the exact identity
`re_five_atom_eq_keep_positive`:

\[
\boxed{\Re f_N(n)=\max(\Re f_N(n),0)
-w_N(n)\,\mathrm{positiveAllowance}(L,n)(-x).}
\]

The weight still contains the original factorial envelope and
`1-boundedShare`. Thus there is no remaining coefficient-estimation slack
on this five-prime phase sector. Its weighted population sum is still an
open arithmetic problem.

`eventually_re_core_ge_four_five_credit` combines this exact debit with
the previously sharpened four-prime inequality in the same source-normalized
core sum. Other prime counts and five-prime positive-cosine terms remain
signed. The theorem is uniform in height and count endpoint, with no
zero hypothesis.

`eventually_compensated_core_floor` also retains the paid balanced triple
band, its positive triple credit, and at least half the disjoint four-prime
supply. The new comparison is applied only to the untouched complement;
it neither reuses nor charges the supply. Only the already controlled
geometric radial-edge error is added. The target remains a floor for the
whole signed combination, not separate decay of its terms.

## Quantitative exploration and rejected alternative

The optional [capacity probe](../scripts/probe_riesz_joint_capacity.py)
and its [recorded output](riesz-joint-capacity-probe.json) retain the same
moving length and model allocation as before. For example:

| Order `N` | Seed | Old clipped positive allowance | Exact positive part |
| --- | --- | ---: | ---: |
| 65536 | 17 | 0.016856 | 0.006292 |
| 65536 | 29 | 0.015864 | 0.006380 |
| 1048576 | 17 | 0.016746 | 0.006208 |
| 1048576 | 29 | 0.015570 | 0.006312 |

These are uncertified coefficient-over-`N` density integrals at `T=2N`,
omitting common radial and phase factors. They are not source-scale bounds
for literal prime sums. Small primes, higher counts, radial transport and
certified integration errors remain outside this diagnostic. The Lean
theorems use none of its output.

An earlier probe dropped the positive three-subset hinges after odd
reflection, retaining the singleton excesses and pair-cutoff deficits.
It captured roughly three quarters of the modeled favorable five-prime
mass but produced **no observed improvement** over the existing joint
lower comparison (only floating-point differences below `1e-15`). That
route was discarded before adding Lean machinery. The probe retains its
results as an audit; no universal dominance theorem is claimed for that
candidate. The exact cofactor identity above directly improves the old
debit instead. All probes remain optional and outside ordinary CI.

The remaining obstruction is the weighted signed population comparison:
unpaid triples, these now-exact adverse five-prime terms, other phase
sectors and higher counts must be controlled together with unused positive
credit. No whole-carrier numerical floor or zero exclusion is proved.
