# The remaining edge loss cannot be a bounded allowance

The joint target remains a cofinal floor for the **whole** `J+C`.
`ZetaRieszJointEdgeLoss` checks the last clipping operation in the improved
signed compensation comparison. It introduces no new carrier and proves
no floor or zero exclusion.

Write `T=log n`, `P=largestPrime n`, `r=minFac n`,

\[
z_N(n)=(1-\theta_N(n))K_N(3/2+iy,n),\qquad
e_L(n)=\max\{0,\log r-\max(0,L-\log P)\}.
\]

The exact theorem
`SignedCompensationBounds.re_atom_sub_compensation_keep_positive` shows
that the previous lower comparison, on its stated pair-separated and
saturated support, loses precisely

\[
\frac{T}{L}\,e_L(n)\max\{-\operatorname{Re}z_N(n),0\}.
\]

This is different from the earlier loss of **all** positive observations.
Although the edge is zero at prime counts at least seven under the proved
remaining geometry, the small counts still prevent a bounded allowance.

For every fixed `y≠0` and `1/2<u<=10001/20000`,
`eventually_edge_loss_growth` proves, on the unchanged dyadic schedule,

\[
u^{N_j+1}\sum_{\substack{n\in\mathrm{coreBand}\\\omega(n)=3}}
\frac{\log n}{L_{N_j}}e_{L_{N_j}}(n)
\max\{-\operatorname{Re}z_{N_j}(n),0\}
\ge k\frac{(2u)^{N_j}}{(N_j+1)^4}
\quad\text{eventually},\qquad k>0.
\]

`edge_loss_tendsto_atTop` proves this three-prime loss tends to infinity.
Thus no bounded allowance can pay it, even at arbitrarily late indices. The
constant and starting index are existential; the theorem does not give
a numerical height or order threshold.

The proof uses actual distinct primes with log slopes `21/50`, `23/50`
and `28/25`. Their total logarithm is near `2N`, and their largest share
is near `0.56`, below both the old and refined allocation transitions.
A bounded translation of the largest-prime interval makes
`cos(y log n)<=-1/2` throughout each product box. The existing prime-count
theorem supplies at least `c exp(2N)/(N+1)^3` distinct integers, with
`c>0`. There is no replacement of the prime measure by a continuum.

For these labels Lean checks all inherited core, physical, count and
nondominant masks. The exact old allocation leaves at least half the
weight eventually. On the actual moving length, `e_L(n)>=N/10` and
`log n/L>=1`. The factorial envelope and prime count then give the
displayed lower bound. These are three-prime labels; their two-prime
cofactor is saturated, and there are no remaining pair-separation tests.

This does **not** show the signed carrier diverges, or that the joint
floor is impossible. It shows that both the unit and its rising-edge
correction must retain their signed observations. The joint arithmetic
floor `-79/1000-o(1)` remains open; neither the new loss bound nor the
previous positive-credit bound is a free signed reserve.

`edge_charged_core_tendsto_atBot` connects the audit directly to the
existing source ledger. Under the same exposed-zero hypotheses used
there, the unchanged normalized core has its proved finite source limit.
Subtracting just the above three-prime loss makes that lower comparison
tend to **minus infinity**. This also rules out a cofinal constant floor
for this particular comparison. It imposes no simplicity assumption and
does not assume the independent arithmetic floor we are trying to prove.
