# Owner-hinge cancellation across all cutoffs and owners

This local slice removes the remaining hinge-height growth from an actual
signed scalar in the masked-carrier estimate. The original cofactor moments,
literal comparison variation, funding and numerical floor remain unpaid.
No source-o(1) population or zero exclusion is newly proved.

Source: [ZetaRieszOwnerHingeCancellation.lean](../RiemannGaussian/ZetaRieszOwnerHingeCancellation.lean).

## What is now bounded independently of the hinge height

The existing scalar multiplying the signed cofactor zeroth moment is

\[
\Lambda_p(c)=\frac{p+1}{p}
\sum_{D\le\lfloor e^c\rfloor}
\bigl((c-\log D)_+-(c-\log(D+1))_+\bigr)
\,\mathrm{roughDensityPrefix}(\{p\},D).
\]

The preceding slice proved \(|\Lambda_p(c)|\le\rho c_+\), with
\(\rho\) the squarefree density. The new checked theorem gives

\[
\boxed{|\Lambda_p(c)|\le7\frac{p+1}{p}\le\frac{21}{2}}
\]

for every actual prime \(p\) and every real moving cutoff \(c\). This is
independent of the hinge height, cofactor count, radius, factorial order
and phase ordinate. The former linear bound remains available for short
or zero hinges.

The existing constant-seven `densityRiesz_bound` is reused, not replaced
by an unproved asymptotic. The new ingredient is the exact bridge from
that signed mean to the owner-conditioned scalar.

## The cancellation principle

Set \(b(n)=\mu(n)\,\mathrm{density}(\mathrm{primeFactors}(n))\). For the
single owner prime, exclude precisely those marks divisible by \(p\).
The coefficient recurrence is exact:

\[
\mathbf1_{p\nmid n}b(n)
=b(n)+\frac1{p+1}\mathbf1_{p\mid n}
\mathbf1_{p\nmid n/p}b(n/p).
\]

For a repeated prime the relevant coefficients are zero. Otherwise the
prime insertion changes the Möbius sign and multiplies the marked density
by \(1/(p+1)\). All parities are retained in this identity.

Finite divisor reindexing and exact summation by parts identify
\(\Lambda_p\) with the excluded signed Riesz mean and prove its recurrence

\[
\Lambda_p(c)=\mathrm{densityRiesz}(c)
+\frac1{p+1}\Lambda_p(c-\log p).
\]

The translated integer cutoff is exactly
\(\lfloor e^{c-\log p}\rfloor=\lfloor e^c\rfloor/p\).
Strong induction on this physical cutoff terminates; no infinite product,
prime completion, phase approximation or convergence hypothesis enters.
The geometric price is

\[
\frac7{1-1/(p+1)}=7\frac{p+1}{p}.
\]

This contraction is for the complete signed reference mean, after
joining all divisor cutoffs and counts. It is not pointwise contraction
of the literal factorial kernel, nor a reversal of the earlier
boundary-renewal no-go.

## Application to the actual masked carrier

Use the SAME owner rows, masks and scaled weight \(w\) as in
`literal_whole_carrier_estimate`, and retain

\[
U_p=\sum_a w(a,p)R_L(a),\qquad V_p=\sum_a w(a,p).
\]

The new `literal_whole_carrier_constant_bounds` gives both directions:

\[
\boxed{
\sum_p\left(\rho U_p-7\frac{p+1}{p}|V_p|\right)-E_N
\le\rho J_B
\le\sum_p\left(\rho U_p+7\frac{p+1}{p}|V_p|\right)+E_N.
}
\]

It holds on every literal \(B\subseteq\mathrm{coreBand}\). The first moment
remains signed. The zeroth-moment price uses \(|\sum_a w(a,p)|\), retaining
cofactor/count/period phase cancellation before its norm. No owner,
squarefree, count, radial, physical or allocation mask is completed.

The error \(E_N\) is still the original
\(6C e^{-N/128}\) times its explicit literal variation. That variation
is unpaid. The theorem does not assume it tends to zero merely because
its prefactor decays. The signed first moment and aggregate zeroth-moment
cost also remain unpaid at source scale.

## Retaining cancellation between owners

The next eight checked proofs join owners as well as their cofactor counts.
Write `R` for the same `densityRiesz` above. The exact recurrence gives

\[
|\Lambda_p(c)-R(c)|\le\frac7p,
\qquad |R(t)-R(s)|\le\rho|t-s|.
\]

The second bound uses the already proved signed density-prefix allowance
`rho`; it sums all divisor signs before charging the cutoff difference.
Consequently, for any actual owner primes,

\[
\boxed{
|\Lambda_p(L-\log p)-\Lambda_q(L-\log q)|
\le\rho|\log p-\log q|+\frac7p+\frac7q.
}
\]

This gives a quantitative cross-owner saving whenever their complete
signed moments cancel. For example, opposite moments `v,-v` at owners
`p,q` cost at most the displayed difference times `|v|`, rather than two
separate constant-seven allowances. It neither asserts those moments are
opposite in the actual carrier nor discards their common source mode.

For the entire actual finite owner set `P`, let

\[
G(k)=\sum_{p\in P,\ p\le k}V_p,\qquad X=\max(1,\max P).
\]

Exact owner summation by parts now proves

\[
\boxed{
\left|\sum_{p\in P}\Lambda_p(L-\log p)V_p\right|
\le C_P:=7|G(X)|
+\rho\sum_{1\le k<X}\log\frac{k+1}{k}|G(k)|
+7\sum_{p\in P}\frac{|V_p|}{p}.
}
\]

Every `V_p` is the complete signed cofactor/count/period sum with all
original masks. The first two terms retain cancellation **across owners**
before the absolute value; only the small exact owner-conditioning
correction has a separate `1/p` price. This allowance can be much smaller
than the earlier separate-owner cost. It is not automatically smaller for
coherent moments: both estimates remain available.

`literal_whole_carrier_prefix_bounds` propagates this to the SAME original
masked carrier on every `coreBand` subset:

\[
\rho\sum_p U_p-C_P-E_N\le\rho J_B
\le\rho\sum_p U_p+C_P+E_N.
\]

The aggregate first moment remains signed. The actual owner-prefix cost
`C_P`, the literal comparison variation in `E_N`, and the funding ledger
are **unpaid at source scale**. No prime-period cancellation theorem is
assumed, no mask or count class is completed, and this is not yet the
independent numerical floor.

The stronger `literal_whole_carrier_centered_bounds` keeps the common
owner resonance **signed and joined with the first moment**. Define only
for this displayed inequality

\[
T_P=\rho\sum_p U_p-R(L-\log X)G(X),\qquad
C_P^\circ=\rho\sum_{1\le k<X}\log\frac{k+1}{k}|G(k)|
+7\sum_{p\in P}\frac{|V_p|}{p}.
\]

Then, on the SAME literal support,

\[
\boxed{T_P-C_P^\circ-E_N\le\rho J_B\le T_P+C_P^\circ+E_N.}
\]

This main term does **not** charge `7|G(X)|` or assert that the resonance
decays. The norm-only variant above is a corollary. The independent next
estimate must control this retained signed joint term with its cumulative
owner variation and funding; bounding the first moment and resonance
separately would lose precisely the correlation this theorem retains.

## Cleaning the comparison extension on the entire unpaid population

The published unpaid support removes dense, few-bin and high-tail
**squarefree** labels. Nonsquarefree labels in those same ranges can remain
in its raw comparison extension. They contribute exactly zero to the
carrier but can create artificial variation in the comparison weight.
The fixed-count deletion was already independent of squarefreeness and
does not have this issue.

The next eight public proofs remove these artifacts across the whole
remaining population. `remainingOwnerBand` aliases the existing published
set; it does not define a new carrier. `comparisonOwnerBand` uses the same
core and the exact tests

\[
\begin{gathered}
56\le\omega(n)<\operatorname{countThreshold}(N),\qquad
\omega(n)<5\log(N+1)+2,\\
|\operatorname{cofactorBins}(N,n/\operatorname{largestPrime}(n))|
>\lfloor\log(N+1)/16\rfloor,\\
\log\operatorname{largestPrime}(n)
<\frac{751}{1250}\log n.
\end{gathered}
\]

These selector tests contain no squarefree indicator. Lean proves the
comparison set is a subset of the original unpaid set and that their
squarefree subsets are **exactly equal**, including zero-coefficient rows.
Consequently the entire original signed sum, owner/cofactor moments,
allocation and phase are unchanged. No population is norm-paid or
completed by this operation.

For the cleaned raw weight `q`, an exact support theorem gives

\[
\begin{split}
\sum_{k\le X}k|q_p(k)-q_p(k+1)|
={}&\sum_{\substack{k\le X:\\
\mathrm{geometry}(pk)\ \lor\ \mathrm{geometry}(p(k+1))}}
k|q_p(k)-q_p(k+1)|.
\end{split}
\]

Thus edges wholly outside the genuine unpaid geometry have **zero**
comparison charge, even when their endpoints are nonsquarefree. Active
edges, including genuine cutoff crossings, are retained in full. Removing
rows does not make arbitrary total variation monotone, so we do not claim
that the new total price is automatically smaller than the old one.

`literal_remaining_centered_bounds` proves both signed bounds for the
original unpaid carrier with this active-edge comparison price. The
common resonance remains inside `T_P`. Finally,
`eventually_joined_centered_owner_floor` spends that bound in the existing
whole-floor ledger:

\[
\frac{T_P-C_P^\circ-E_N^{\mathrm{active}}}{\rho}
+u^{N+1}\left(
\max\Re\mathrm{Paid}+\max\Re\mathrm{Tail}
-\mathrm{debit}_N\Re\mathrm{Supply}\right)-e_j
\le\Re\bigl(u^{N+1}\mathrm{joinedPhysical}\bigr).
\]

Both maxima have the original zero alternative, and every debit and supply
is precisely the already proved ledger term. The same vanishing `e_j` is
used: the support cleanup incurs **no additional error** or funding credit.
There is no assumed Type-II, orthogonality or phase-cancellation estimate.

The actual centered joint main, cumulative owner cost, active-edge
comparison variation and funding still need quantitative control. This is
not a source-normalized decay theorem for the comparison error, a newly
paid nonzero population, or a proof of the numerical floor.

## Why active-edge absolute variation still fails

The cleanup does not remove the **canonical-owner** restriction. Fix an
actual owner prime `p` and write `w(a)` for the same raw masked weight.
If a prime `q>p` divides `a`, then `p` cannot be the largest prime of `pa`,
so `w(a)=0`. This is independent of squarefreeness and retains every count,
bin, radial, phase and allocation condition.

Bertrand's theorem supplies `p<q<=2p`. Telescoping to the next multiple of
`q`, then summing without changing the finite support, gives

\[
\sum_{a\le X}a|w(a)|
\le 2p\sum_{a\le X}a|w(a)-w(a+1)|.
\]

On the literal core `log(pa)>39N/20`. For a column with `log p<=N/2`,
every nonzero weight therefore has `a>=exp(29N/20)`. Consequently the
**current** comparison allowance satisfies the checked lower bound

\[
\boxed{
\frac12 e^{603N/640}\sum_{a\le X}|w(a)|
\le e^{-N/128}\sum_{a\le X}a|w(a)-w(a+1)|.
}
\]

`comparison_owner_active_allowance_lower` proves the same inequality for
the cleaned **active-edge** price, with the original unpaid geometry
retained. Thus the explicit `exp(-N/128)` prefactor does not supply a
small comparison cost relative to this column's absolute mass. The cause
here is the largest-prime ownership restriction, rather than the
nonsquarefree rows removed by the cleanup.

This is a lower bound on a **positive majorant**, not on the actual signed
comparison error or carrier. No population-mass lower bound is proved;
in particular this theorem does not assert that the actual error diverges
or disprove the floor. The useful remaining target is cancellation in the
signed discrepancy across original labels/owners before taking absolute
values, or a reference measure that itself preserves the ownership zeros.
Many-bin occupancy alone does not estimate either target.

The four additional public proofs are
`raw_owner_weight_zero_larger_prime`, `raw_owner_variation_lower`,
`raw_owner_allowance_lower` and `comparison_owner_active_allowance_lower`.

## Numerical regression and checks

`scripts/probe_riesz_owner_hinge.py` evaluates the scalar on actual integer
prefixes for five owner primes and three cutoffs, through50000. It checks
the recurrence and the constant allowance. The finite Euler density and
tail enclosure are floating diagnostics, not rigorous interval
certificates. Five additional cases evaluate the actual-integer reference
scalars with prescribed signed owner amplitudes, testing the joint prefix
allowance and including a coherent case where it is worse. These amplitudes
are **not measured carrier moments**. For opposite amplitudes at owners
10007 and10009, the new price is about0.000109 times the former separate
price; this illustrates the coefficient saving, not a floor credit. The
probe contains no literal masked-carrier estimate and is outside ordinary CI.

All twenty-four public Lean theorems have focused warning-as-error direct,
targeted build, root import, namespace-lint and standard-axiom audits.
See `riesz-owner-hinge-cancellation-audit.json`. Public README/explorer
endpoints are unchanged; wider publication checks remain deferred.

The independent \(-79/1000\) floor remains open. The concrete saving is
that the complete owner-hinge multiplier no longer grows with its
cutoff; this is not a percentage of the final floor gap or an exponential
saving for the masked carrier. The additional concrete gain is that the
bound now exposes cross-owner cancellation through `G`, rather than losing
it in `sum_p |V_p|`. Many-bin occupancy alone does not bound this profile.
