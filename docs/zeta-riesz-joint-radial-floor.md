# Paying allocation errors with joint radial information

[`ZetaRieszJointRadialFloor`](../RiemannGaussian/ZetaRieszJointRadialFloor.lean)
proves additional bounds for the **actual finite sum**, uniformly for
`0 <= u <= U = 10001/20000` and every real height. It combines the total
logarithm with the allocation tail before taking the summable envelope.
No new carrier is defined. The original core masks, complex phase and
prime-count range are retained.

Put `T = log n`, `sigma = 1+1/262144`, and let `M_sigma` denote the existing
finite `zetaMoebiusLogMajorantMass sigma`. Its numerical size is unevaluated.

| Part paid | Prime-share condition | Additional total-log condition | Source-normalized norm bound |
|---|---|---|---|
| Residual `(1-boundedShare)*c_L` | Some eligible physical prime has share at least `3/5` | `T <= 248N/125` or `252N/125 <= T` | `2 M_sigma exp(-N/400000)` for `N >= 320` |
| Assigned part `boundedShare*c_L` | Every eligible selected prime has share at most `59/100` | `T <= 987N/500` or `507N/250 <= T` | `4U(N+1) M_sigma exp(-N/400000)` |

The second row pays removal of the allocation factor on that subband.
**It does not bound the remaining raw signed Riesz sum.**
The first row also retains the physical condition `log p <= L_N`; the
actual core supplies it. On the original cofinal schedule,
`remaining_prime_log_lt_radial` discharges eligibility from the literal
masks and shows every prime in a nonzero remaining outer-radial atom has
share strictly below `3/5`.

## Why this passes the earlier tilt barrier

The earlier [all-tilt obstructions](zeta-riesz-joint-dominant-floor.md)
are preserved. They use a share-only kernel envelope which loses the
actual value of `T/N`. The new joint exponent, at a radial endpoint `t`, is

\[
\log(Ut)+1-\frac{131071}{262144}t-\delta.
\]

Lean checks this is at most `-1/400000` at both relevant endpoints:

- residual: `delta=1/12500`, tilt `41/40`, endpoints `248/125`, `252/125`;
- assigned: `delta=1/35000`, tilt `197/200`, endpoints `987/500`, `507/250`.

The lower/upper factorial Chernoff estimates then apply on the respective
whole outer intervals. The residual's lower missing allocation tail is
still paid by its physical cutoff and the existing `exp(-N/2000)` saving.
Nothing here asserts decay at the central saddle `T=2N`.
The subsequent [exact-tail audit](zeta-riesz-joint-tail-audit.md) proves
growth of the actual source-scaled binomial tails there, not just failure
of a selected upper envelope. It does not estimate the signed prime sum.

The [optional probe](../scripts/probe_riesz_joint_radial.py) records
[floating-point diagnostics](riesz-joint-radial-probe.json), including the
positive central exponents. The rational Lean inequalities are the proofs;
the numerical output is not a prime-sum or quadrature certificate.

## One signed inequality, with the complement retained

`norm_residual_union_le` and `norm_assigned_union_le` take the union of these
regions with the earlier share-only regions (`0.601` and `0.586`, respectively).
No earlier coverage is lost.

Let `S` be the existing core after deleting only that paid high-share union.
Choose `D` inside `S` in the paid assigned-part union. With
`b_n=c_L(n)K_N(3/2+iy,n)`, `re_core_ge_joint_reduced` proves

\[
\operatorname{Re}(u^{N+1}\mathrm{coreResponse})\ge
\operatorname{Re}\left(u^{N+1}\left[
\sum_{n\in D}b_n+
\sum_{n\in S\setminus D}(1-\theta_N(n))b_n\right]\right)-E_N.
\]

Writing the earlier assigned rate as
`r=U*(262144/131071)*exp(-1/8200)<1`, the explicit allowance is

\[
E_N=M_\sigma\left[
4U(N+1)\left(r^N+e^{-N/400000}\right)
+2\left(e^{-N/1000000}+e^{-N/400000}\right)\right]\longrightarrow0.
\]

`tendsto_joint_allowance` proves the displayed limit. Both retained sums
remain inside **one real observation**; neither is assumed nonnegative or
small. The raw signed contribution, central allocation transition, and
[joint cofinal floor](zeta-riesz-joint-floor.md) `-79/1000-o(1)` remain open.
This slice proves no new zero exclusion and does not change the public RH
source endpoint.
