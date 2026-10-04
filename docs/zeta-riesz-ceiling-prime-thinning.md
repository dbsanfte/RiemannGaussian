# Complete-prime coverage: an algebra-first detector control

The full `42/25` ceiling on the original fixed radius interval remains
**open**. This control supplies **zero ceiling credit** and no zero exclusion.
It strengthens the earlier continuous and integer controls by using genuine
ordinary primes at `u=10001/20000`, with one fixed height `y=54`.

The checked module is
[ZetaRieszCeilingPrimeThinningAudit.lean](../RiemannGaussian/ZetaRieszCeilingPrimeThinningAudit.lean).
It does not change `joinedPhysical`, its masks, the exposed-zero assumptions,
the paid errors or the requested endgame constant.

## Exact arithmetic construction

Write `delta=u-1/2>0`. On actual primes define

\[
w(p)=\min\{1,4p^{-\delta}(1+\cos(y\log p))\}.
\]

Both the removed weight `w` and retained weight `1-w` lie in `[0,1]`.
Every term uses the original common phase and logged factorial kernel,
including orders zero and one:

\[
A_k=\frac{u^{k+1}}{k!}\sum_p(\log p)^{k+1}p^{-3/2-iy},\qquad
D_k=\frac{u^{k+1}}{k!}\sum_pw(p)(\log p)^{k+1}p^{-3/2-iy}.
\]

The retained arithmetic series is `A_k-D_k`. The exact checked ledger is
`retainedMoment + clippedRemovedMoment = ordinaryArray`.
It is not legitimate to omit `D_k` just because every retained label is prime.

Before clipping, the removal is exactly three convergent ordinary-prime
series. With

\[
T_k(v)=u^{k+1}\operatorname{ordinaryMoment}_k(1+u+iv),
\]

the checked pointwise and complete-series identities give

\[
D_k^{\rm raw}=4T_k(y)+2T_k(0)+2T_k(2y).
\]

Lean proves `T_k(0)->1` and `T_k(v)->0` at every fixed nonzero `v`.
The proof removes the genuine pole with `riemannZeta₁`, enlarges its compact
zero-free disk, applies Cauchy bounds to that analytic remainder, and pays
proper prime powers independently. It assumes no hypothetical zero or
prime-density approximation.

Clipping changes only a finite prime head: `w_raw(p)<=8p^(-delta)`, so it
is already at most one once `delta*log p>=log 8`. The complete normalized
finite-head difference is proved to tend to zero. Thus `D_k->2`.

At fixed height `54`, the repository's independently proved concrete radius
`100011/200000>u` gives `A_k->0`. Consequently the retained fractional
prime series tends to `-2` **unconditionally**.

Evaluating the unchanged algebraic ceiling expression
`-traceError(a,N-1)-harmonicEvaluation(a,u,N)` on this retained series gives

\[
-2+4c_{\rm ret}(10001/20000)
=1.68051281186022328837\ldots>42/25.
\]

`retained_join_exceeds_ceiling` proves the eventual strict reverse inequality.
This is a control for the **joined evaluator on a thinned fractional prime
measure**, not a counterexample to the complete ordinary-prime ceiling.
The complete-prime source identities and physical-mask payments are not
transferred to the thinned model.

## Unit-prime rounding and its separate limit question

For integer endpoints let

\[
F(M)=\sum_{p<M}w(p),\qquad
b_p=\lfloor F(p+1)\rfloor-\lfloor F(p)\rfloor.
\]

Lean proves `b_p in {0,1}`, `b_p=0` at composites, exact cumulative
telescoping, and prefix discrepancy below one. This is rounding the actual
prime count, not a continuous count on composite integer generators.

The **infinite binary factorial-moment Abel bridge is not formalized here**.
The binary finite probe is therefore not claimed as a cofinal witness. The
unconditional cofinal reverse inequality above is for fractional weights.

## Detector bookkeeping before statistics

The optional
[probe](../scripts/probe_riesz_ceiling_prime_thinning.py)
first imports the frozen exact component collector. Across 72 cases it keeps
the prime identity attached to each factorial order, combines swapped whole
legs, checks the repeated-prime diagonal once, and verifies the cancellation
of every order-zero endpoint. It also runs 127 exact endpoint-incidence
checks. No statistical fit is used to establish these cancellations.

Only then does it evaluate all 82,025 primes through `2^20` at the target
radius. Cumulative rounding removes 69,695 and retains 12,330 unit prime
atoms. Nine moment rows keep logged orders `0,1,2,4,8,12,16,24,32`.
Seven finite joined rows use the exact rational floor
`floor(u^(-N)/(N+1))` in the repository's moving Riesz length. Each joined
row retains the removed linear term, removed quadratic term, and both mixed
retained/removed incidences: their sum recovers the complete finite join.

The [independent checker](../scripts/check_riesz_ceiling_prime_thinning.py)
regenerates the primes using FLINT primality, uses direct factorial recurrence
instead of logarithmic gamma evaluation, and replays all nine moments,
seven joins, the exact moving floors and 127 endpoint checks. Kernel spot
checks and 24 cumulative floor decisions use 85-digit arithmetic in the
producer. They are not ball certificates for every floating floor decision.

The finite rows do not establish the eventual source crossing, estimate its
entry order, or quantify the unpaid literal carrier. They demonstrate a
detector failure mode: actual prime support and unit sample weights do not
certify complete-prime coverage. A proposed saving must account for its
omitted signed terms and mixed incidences before taking norms or scanning
features.

The focused leaf, 14 namespace linters and transitive-axiom check are optional
local checks. This slice does not register a root import, run wider gates,
alter prior snapshots, commit, push or update public theorem metadata.
