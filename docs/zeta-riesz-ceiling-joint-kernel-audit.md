# Joined moving-kernel norm-payment audit

The original independent ceiling remains **42/25 for the native joined
carrier, throughout the original candidate strip and at all heights**.
This leaf supplies a new method obstruction, **zero new arithmetic ceiling
credit**. It preserves the actual sparse-cluster payment and every earlier
no-go. The dense signed divisor and unrestricted heights remain open.

The [Lean leaf](../RiemannGaussian/ZetaRieszCeilingJointKernelAudit.lean)
rules out a positive Laplace-price strategy even after all moving complex
coefficients have been collected. It does not bound, identify, or disprove
the ceiling of the actual signed prime carrier.

## Exact all-family tradeoff

For an arbitrary complex kernel, define

\[
B_d(f)=\int_0^\infty |f(t)|e^{-dt}\,dt,
\qquad
S_d(f)=\int_0^\infty f(t)e^{-dt}\,dt.
\]

All norms here are taken **after joining the entire kernel**, not per
coefficient, prime, incidence, count, or factorial order. Suppose
\(a<u<q\), each of these three prices is integrable, and
\(|S_u(f_N)|\ge1\). The exact split at any real \(T\) gives

\[
1\le B_u(f_N)
\le e^{(q-u)T}B_q(f_N)+e^{-(u-a)T}B_a(f_N).
\]

Consequently, if \(B_q(f_N)\to0\), then

\[
\boxed{B_a(f_N)\longrightarrow+\infty.}
\]

`price_split`, `eventually_price_lower`, and `price_tendsto_atTop`
prove this for **every moving family** of complex kernels satisfying those
explicit hypotheses. There is no fixed-degree, coefficient-growth,
positivity-of-the-kernel, or uniform-integrability assumption. In particular,
the result is stronger than the earlier fixed-filter norm-budget audit.

For the repository's exact polynomial kernel

\[
f_N(t)=u^{N+1}\operatorname{zetaFactorialPolynomial}(P_N,N,t),
\]

the genuine factorial Laplace theorem proves
\(S_u(f_N)=P_N(1/u)\); integrability at every positive damping is automatic.
`joint_polynomial_price_tendsto_atTop` permits arbitrary moving polynomial
degrees and coefficients, retaining all moment-order shifts. The source
normalization \(P_N(1/u)=1\) is explicit. No complete-prime density or
literal-mask bridge is assumed.

## Quantitative audit at the original upper radius

At \(a=1/2\), \(u=10001/20000\), \(q=7/10\), if
\(B_q(f_N)\le e^{-N/32}\), the exact joined inequality gives

\[
\boxed{B_{1/2}(f_N)\ge\tfrac12e^{N/255936}\quad(N\ge64).}
\]

For \(N\ge400000\), `original_radius_price_exceeds_target` proves this
positive method price exceeds \(42/25\). This is **not** a lower bound
for any actual prime norm, the literal signed carrier, or its real part.
It cannot be transferred through a density approximation.

## Algebraic regression before numerical scanning

The adjacent-order filter

\[
P(X)=10001-\frac{10001}{2}X
\]

has exactly \(P(1/u)=1\) and \(P(2)=0\). Its two collected Laplace slots
are \(10001-10000=1\) at the selected damping and
\((2u)^{N+1}(10001-10001)=0\) at the real-axis pole damping.
The probe retains both factorial indices \(N,N+1\), their common factor,
and the **\(u^{N+1}\)** normalization before any norm is evaluated.
Thus the failure is not missed endpoint cancellation or a coefficientwise
triangle inequality.

After collection the full kernel's positive price is exactly

\[
B_{1/2}(f_N)
=(2u)^{N+1}\,10001\,
\frac{2(N+1)^{N+1}e^{-(N+1)}}{(N+1)!}.
\]

At \(N=4096\) it is approximately **187.7860066163**, even though the
signed real-axis pole response is exactly zero. This scalar model is not
an actual-prime or zero sample and measures no unpaid carrier mass.

The probe also checks arbitrary Gamma-shaped moving kernels with exact
selected response one. A linear-in-order rate keeps the lower price
bounded, but its separated price tends to the **nonzero** value
\(e^{-(q-u)}\); it therefore fails the hypothesis needed to pay the
separated analytic budget. Bounded separated price alone is insufficient.

## Verification and next arithmetic target

Optional local checks:

```sh
/home/dbsanfte/.elan/bin/lake env lean scripts/CheckRieszCeilingJointKernelAudit.lean
../.venv/bin/python scripts/probe_riesz_ceiling_joint_kernel.py \
  --output .lake/riesz-ceiling-joint-kernel-audit/probe.json
../.venv/bin/python scripts/check_riesz_ceiling_joint_kernel.py \
  .lake/riesz-ceiling-joint-kernel-audit/probe.json \
  --output .lake/riesz-ceiling-joint-kernel-audit/numeric-replay.json
```

The independent replay uses exact rational slot collection and 420-bit Arb
intervals. Neither script runs in ordinary CI. The scoped proof audit checks
14 linters and all transitive axioms. The JSON audit pins every previous
source/proof/probe artifact and leaves concurrent semiprime work intact.

This result closes the generic **positive Laplace norm-payment route**,
not the signed arithmetic endgame. Next work must use an independently
proved correlation of the complete prime measure or the actual signed
divisor, with phases and complementary contributions retained. Retuning
moving degrees cannot bypass the stated tradeoff. The selected source,
all literal masks, orders zero and one, native evaluator, and all-height
objective remain unchanged. No zero exclusion or native entry order is
claimed.
