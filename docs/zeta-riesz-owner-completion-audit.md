# Shared-owner completion: the prime boundary reinforces

Local audit, 2026-10-03. The objective remains **Close out the floor**.
The independent cofinal floor `-399/5000`, ceiling `42/25`, restricted
contradiction and RH remain open. This slice rules out a completion
shortcut; it does not prove a saving on the remaining global debit.

## Native theorem

[ZetaRieszOwnerCompletionAudit](../RiemannGaussian/ZetaRieszOwnerCompletionAudit.lean)
uses the actual owners and integer pair intervals from the SAME full
ordinary-prime correction. For

\[
  \tfrac12\le u\le\tfrac{10001}{20000},\qquad N\ge65536,
\]

every original pair has

\[
 \log p\ge\tfrac{51}{50}N,\qquad
 \tfrac7{10}N<\log q\le\tfrac{101}{100}N,
 \qquad \tfrac{277}{200}N\le L\le\tfrac{139}{100}N.
\]

Completing the cofactor row at its smaller prime `q` returns the
ordinary-prime cofactor `p`. Its **literal** divisor response is

\[
 R_{L-\log q}(p)=L-\log q\ge\tfrac38N>0.
\]

The original correction's coefficient is
`(L-log p)*ownerWeight N (log q/(log p+log q))`. The exact factorial
allocation stays in `[0,1]`, and this coefficient is nonnegative and
no larger than the new boundary coefficient. The earlier theorem
that a joined marked weight vanishes on two-prime labels does not
make this different, literal prime-cofactor response vanish.

Both channels have **the identical product phase**. For their common
nonnegative factorial/sieve amplitude `w`, the theorem states

\[
 \left\|wR_{L-\log q}(p)e^{-iy\log(pq)}
    +w(L-\log p)\,\mathrm{ownerWeight}_N
      e^{-iy\log(pq)}\right\|
 =w\left[R_{L-\log q}(p)+(L-\log p)\,\mathrm{ownerWeight}_N\right].
\]

`originalPair_boundary_norm_add` proves this directly with the original
complex head atom, its exact allocation, radial kernel and sieve. In
the completion ledger both boundaries are subtracted. Consequently
they reinforce on identical labels. **Cancellation across different
labels remains possible and unbounded**; this is not a theorem that
their whole signed sum fails to decay.

## Finite go/no-go probe

The optional [probe](../scripts/probe_riesz_owner_completion.py) exhausts
the frozen toy intervals at `N=6,7,8`, heights `54,65,100`, and both the
full `1.95..2.03` window and contracted `1.971..2.029` main window.
The original correction always keeps its FULL window. All 18 frozen
complex-total regressions pass.

It retains the full phase and factorial weights, squarefreeness and
coprimality. The cofactor density is the existing squarefree-integer
divisibility density, **not prime density**. The original main is the
allocation-free comparison whose allocation DIFFERENCE is paid in the
native chain; the original correction keeps its exact allocation.

The probe's exact finite ledger (floating evaluation) is

\[
 M-H_{\rm old}
 =M_{\rm rest}+E+D-H_{\rm new}-T_{3,\rm nonowner}-H_{\rm old},
\]

where `E = completedCompositeRow + H_new - D`. The nonowner
higher-count incidences have exactly zero **integer cutoff signature**.
The nonowner three-prime boundary remains explicit. Every original head
label in the tested main window is matched exactly once in `H_new`;
off-head new prime pairs remain explicit too. Nothing is averaged over
pair incidences or declared paid by `E`.

| Toy order | Matched labels, full / central | Smallest new / old amplitude |
|---|---:|---:|
| 6 | 918 / 777 | 1.03743 |
| 7 | 12595 / 10212 | 1.04005 |
| 8 | 128790 / 103835 | 1.23378 |

The new boundary is not an error term. For example, at `N=8`, `y=65`
in the central window its complex magnitude is about `2.05e-4`, while
the counting discrepancy is about `9.52e-7`. The unchanged actual joint
real total is still `-1.2809138968923752e-4`. These finite numbers are
diagnostics, **not native asymptotic estimates or percentages of the
floor deficit**. Toy length is `-2N log u`; the native integer moving
length, dyadic schedule and full deletion masks are not simulated.
No eventual comparison budget is applied at these toy orders.

## Consequence for the next estimate

Stop the proposed owner-free completion as an automatic payment. The
ordinary-prime count-one boundary survives, and the existing correction
does not cancel it on their common labels. Neither can be charged to the
already-proved squarefree counting error.

The independent signed bound is still required for the original whole
balanced main minus the SAME full correction. The surviving owner profile,
nonowner triples, nonshared main and global correlations are unpaid.
This audit introduces no new floor carrier, completion hypothesis or
source-o(1) claim. Prior geometric allocation/radial/operator errors remain
difference estimates charged once.

Validation is local: strict Lean leaf, targeted build, frozen compiled
ordinary root plus explicit leaf, namespace lint and all-declaration
standard-axiom checks. See
[audit metadata](riesz-owner-completion-audit.json). No root registration,
public endpoint changes, commits, pushes, subagents or wider gates.
