# Signed complete-window owner cancellation

Local work after `194a361762f404a8f4473298b25d96fbae0bb56e`. The independent
whole floor **−399/5000**, ceiling **42/25**, restricted contradiction and
RH remain open. No publication or public endpoint change is made.

This slice proves an independent signed estimate on **literal** complete
owner rows with a small cofactor prime, with all cofactor counts joined.
The argument keeps the exact original binomial allocation and product
phase. It first evaluates the whole smooth oscillatory sum, then bounds
its signed density scalar. The squarefree and forbidden-prime holes stay
in the counting measure throughout.

The four proof files are:

- `ZetaRieszOwnerPhasePrimitive`: exact factorial phase primitive and
  geometric exterior-endpoint estimate.
- `ZetaRieszOwnerLatticePhase`: ordinary integer sampling, exact rounded
  core endpoints and a signed smooth integer-sum estimate.
- `ZetaRieszTaggedOwnerPhase`: the signed tagged density main, joined
  over the owner primes and small tags.
- `ZetaRieszTaggedCoreWindow`: complete **literal** rows, least-prime
  tagging and the actual native count crop.

## The signed phase saving

Write `c = log p`, `z = 1/2 − i y` and retain the existing owner weight

\[
w_N(x)=1-\sum_{k\in\mathrm{unpaidOrders}(N)}
  {N+1\choose k}x^k(1-x)^{N+1-k}.
\]

No factorial order or binomial tail is deleted. After multiplication by
the full factorial phase, the exact expression is the finite polynomial

\[
f_{N,c,z}(T)=\frac{e^{-zT}}{N!}
\left[T^{N+1}-\sum_k{N+1\choose k}c^{N+1-k}(T-c)^k\right].
\]

`ownerPhase_eq_weight` identifies this with
`w_N((T−c)/T) * exp(−zT) * T^(N+1)/N!` exactly. Its finite primitive
`ownerPrimitive` has derivative `−f`. Consequently the **signed whole
integral** is precisely the difference of two endpoint values. Only that
difference is norm-bounded; an absolute interior Fourier/phase allowance
is not used.

If `c>=0`, `c<T` and `2(N+1)<=|z|(T−c)`, the primitive obeys

\[
|\mathrm{ownerPrimitive}_{N,c,z}(T)|
 \le \frac4{|z|}\frac{e^{-T/2}T^{N+1}}{N!}.
\]

For `N>=1`, `0<=c<=4N/3`, `|y|>=54` and
`0<=u<=10001/20000`, the two original core endpoints give

\[
\left|u^{N+1}\int_{1.95N}^{2.03N} f_{N,c,z}(T)\,dT\right|
 \le \frac2{27}(N+1)u\frac{199}{50}e^{-N/200000}.
\]

This is a genuine geometric source-scale saving, rather than another
polynomial improvement to `(2u)^N`.

## Ordinary integer sampling, with rounding retained

The literal smooth test is

\[
g_{N,c,y}(a)=\frac1a,w_N\left(\frac{\log a}{c+\log a}\right)
 \frac{e^{-(c+\log a)/2}(c+\log a)^{N+1}}{N!}
 \cos\bigl(y(c+\log a)\bigr).
\]

Its full derivative, including the old allocation derivative, is bounded
by `[2(N+1)+2+|y|]*radialCap(N)/a^2`. The elementary integer-versus-integral
error is at most `(X−M)` times that derivative bound on the row.
`ownerTest_integral` performs the logarithmic substitution exactly.
This is ordinary lattice sampling, not a prime-density approximation or
generic absolute Abel transport of the masked arithmetic measure.

Set

\[
M_p=\lfloor e^{1.95N-\log p}\rfloor,\qquad
X_p=\lfloor e^{2.03N-\log p}\rfloor.
\]

`coreFloor_membership` proves that `M_p<a<=X_p` is exactly the original
total-log window for positive integers. Both floor errors are retained.
For `N>=64` and `1<=log p<=4N/3`,

\[
\left|u^{N+1}\sum_{M_p<a\le X_p}g_{N,\log p,y}(a)\right|
 \le B_N(u,y),
\]

where

\[
B_N(u,y)=\frac2{27}(N+1)u\frac{199}{50}e^{-N/200000}
 +2u(N+1)[2(N+1)+3+|y|]e^{-N/4}.
\]

Every fixed polynomial times `B_N` tends to zero.

## From the signed main to literal rows

The existing `taggedOwnerRow` contains the original residual coefficient
with canonical singleton ownership, its exact unassigned fraction, the
full complex product phase (then its real part), squarefreeness,
composite-cofactor restriction, forbidden-prime exclusions and a retained
prime divisor `r|a`. No cofactor series or ordinary-prime head is completed.

Complete core rows are partitioned into at most `N` capped dyadic
intervals. On these intervals the already-proved centered comparison has
the **same** signed tagged density scalar. The mains therefore join back
to the whole signed integer sum before any estimate. The ordinary-prime
cofactor head cancels exactly because `r<=M_p<a`.

Let `T` consist of primes through the declared `N^3` ceiling, `V` be a
subset of retained tags and `S(r) subset T` the exclusions. With the
comparison geometry below, the **literal**, joined owner-row sum satisfies

\[
\left|u^{N+1}\sum_{p\in P}\sum_{r\in V}\mathrm{taggedOwnerRow}_{S(r)}\right|
 \le 20uC(6+|y|)(N+1)^6e^{-3N/500}
       +10(N+1)^5 B_N(u,y).
\]

Here `C` is the previously proved positive counting constant. This entire
budget tends to zero. The growing tag count and harmonic owner cost are
funded **after** the geometric signed cancellation. The error uses the
existing subexponential sieve-cost absorption for primes through `N^3`.

The explicit hypotheses are `0<L`, eligible prime owners `p in A`,
`1<=log p<=4N/3`, `log p<=L`, `log Q<=2.03N` for `p<=Q`,
`N^3<=M_p`, `X_p<p`, and positive integer cutoffs `R_p` with
`R_p<=M_p`, `R_p^4<=M_p^3` and `L−log p<=log(R_p+1)`.
The eventual sieve-absorption start is existential, not a sampled native
order. These geometry hypotheses are not asserted automatically for every
remaining carrier label.

## Least-prime consolidation and count crop

Choose `S(r)={q in T : q<r}`. Each cofactor with a prime from `T` then
has a unique least tag, even if it contains many more primes from `T`.
`leastTag_partition` and `selectedRows_sum` prove exact disjointness and
weighted recombination. This removes the earlier **exactly one** small
prime restriction, without a count-by-count allowance.

If `T` contains every prime through `N^3` and retained tags exceed `N^2`,
`leastTag_physical_prime_support` proves the original lower physical
prime restriction for the cofactor. Its upper prime bound below the
owner follows from `a<p`. The concrete owner-log interval
`51N/50<=log p<=5N/4` makes `X_p<p` and the original nondominant inequality
automatic throughout the complete core window.

`eventually_cropped_selected_core_bound` retains the actual count mask
`omega(n)<countCeiling(j)` on the unchanged dyadic schedule. Its bound is
`taggedCoreBudget(u,y,N_j)+allowance(j)`, which tends to zero. The deleted
high-count labels are charged once to the existing independent count
allowance, using unique owner incidences. This is not an additional count
credit or a license to remove other masks.

## Remaining whole-floor obligations

The global floor has not closed. The result does not cover:

- **fully `N^3`-rough cofactors**, which have no small tag; their literal
  ordinary-prime cofactor head must still be kept signed;
- owners below their whole cofactor and other rows that fail `X_p<p`;
- arbitrary internal/share masks that turn a complete window into partial
  intervals with interior, potentially source-sized endpoints;
- any remaining original-mask alignment needed to insert this particular
  population into the whole native cutoff-price ledger.

No claim is made that this population is a fixed fraction of the floor
deficit. The balanced-triple obstruction and all previous no-go audits
remain available. The signed native remainder still needs an independent
bound. `restAllowance` remains divergent; it is not the next strategy.

## Optional regression and validation

`scripts/probe_riesz_owner_phase_primitive.py` is outside builds and CI.
Its twenty continuous cases retain the old selector, both literal core
endpoints and moving total log, but omit the arithmetic counting measure
and density scalar. At `N=1048576`, `y=54` and owner-log slopes `1.025` or
`1.10`, the floating normalized integral norm is about `4.98e-5`; this is
not a native floor certificate. The proved general upper bound is much
looser at that finite order. The slope `1.30` cases are not claimed to
satisfy the full nondominant mask. Truncated-series tail controls do not
certify floating roundoff.

Three integer toys check the exact finite primitive and elementary
sampling error; their original core-window hypotheses fail. An additional
exact integer regression checks least-tag partitioning with several small
primes. It is also a toy, not an application of the native geometry.

See `docs/riesz-owner-phase-audit.json` for focused strict Lean/build,
compiled ordinary-root plus explicit-leaf namespace lint and transitive
axiom checks, with source/artifact snapshots. No wider gates, root-source
rebuild, README/explorer changes, commit, push or subagents are included.
