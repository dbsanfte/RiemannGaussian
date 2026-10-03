# Exact cancellation of the prime head in one-small-prime owner rows

[ZetaRieszTaggedOwnerComparison](../RiemannGaussian/ZetaRieszTaggedOwnerComparison.lean)
pays the **centered comparison error** for the original unique-owner
population with exactly one selected small cofactor prime. The signed
main remains explicit. The whole numerical floor is still open.

## The cancellation is arithmetic

For a finite forbidden-prime set `S` and a tag `r`,

$$
\operatorname{taggedSieve}(S,r,a)
=\operatorname{sieve}(S,a)-\operatorname{sieve}(S\cup\{r\},a)
=\mathbf1_{a\ \mathrm{squarefree}}
 \mathbf1_{\forall q\in S,\ q\nmid a}\mathbf1_{r\mid a}.
$$

Squarefree/rough/divisibility holes stay in the counting measure. They
are not inserted into the smooth test weight or charged as its variation.
The exact old finite binomial owner selector, every factorial order and
the product phase `cos(y*(log p+log a))` are unchanged.

On a complete row `M<a<=X<p` with `r<=M`, a prime cofactor divisible by
the prime `r` would have to equal `r`, outside the row. Thus
`tagged_prime_head_eq_zero` cancels the two **literal** ordinary-prime
heads exactly. This is specific to these marked rows. It does not delete
the prime head from the unmarked rough-owner comparison.

For squarefree `a` divisible by `r`, `tagged_riesz_two_hinges` also gives

$$
\mathcal R_b(a)=
\mathcal R_b(a/r)-\mathcal R_{b-\log r}(a/r).
$$

Both cutoffs and their signs remain together. No prime-count classes,
factorial allocations or translated hinges are given separate allowances.

## The checked global error

Let `T` be any finite set of small primes through `N^3`, and `V` any
subset of retained tags. For tag `r in V` put `S=T.erase r`.
Requiring no prime of `S` to divide the cofactor selects
exactly one prime of `T`. `unique_small_tag` and `tagged_rows_injective`
prove that the tags and unique largest-prime owners do not duplicate a
physical label.

With `b_p=L-log p` and the original shell weight `w_p`, define

$$
\begin{aligned}
\mathcal D_{r,p}
&=\sum_{D=1}^{R_p}
 \bigl((b_p-\log D)_+-(b_p-\log(D+1))_+\bigr)\\
&\qquad\cdot
 \left(\operatorname{roughDensityPrefix}(T\setminus\{r\},D)
       -\operatorname{roughDensityPrefix}(T,D)\right),\\
\mathcal M_{r,p}
&=\frac{\mathcal D_{r,p}\sum_a w_p(a)}{Lp}.
\end{aligned}
$$

This is one **signed** density difference times one **signed** smooth
weight sum. The density scalar and phase sum are not norm-paid separately.
Let `B_{r,p}` be the literal original owner row `taggedOwnerRow`.
`eventually_joint_one_small_owner_error` proves

$$
\left|u^{N+1}\left(\sum_{p,r}B_{r,p}-\sum_{p,r}\mathcal M_{r,p}\right)\right|
\le
8uC(6+|y|)(N+1)N^3(1+203N/100)e^{-3N/500}.
$$

`tagged_comparison_budget_tendsto` proves that the entire right side tends
to zero. `C` is the existing squarefree counting constant. All cofactor
counts and tags are assembled first; this is not a norm bound for the
source-carrying main. The `N^3` tag cost is charged only to the centered
error. The owner cost remains harmonic, `sum_p 1/p`.

The declared geometry is explicit, for every selected owner:

- `N>=32`, `0<M<X<=2M`, `X<p`, `N^3<=M`;
- `R_p<=M`, `R_p^4<=M^3`, `exp(N/2)<=M`;
- `0<L`, eligible prime `p`, `log p<=L`, `L-log p<=log(R_p+1)`;
- `0<=u<=10001/20000`, owner endpoint `log Q<=203N/100`.

The tag sum is over `V`, so the original lower physical threshold can be
retained by choosing `V` above `N^2`. If `T` contains every prime through
`N^3`, `tagged_physical_prime_support` proves that **every** cofactor prime
is above `N^2` and below the original owner. The owner eligibility supplies
the remaining upper physical endpoint. This is a proved implication,
not an assumption that an arbitrary tag set enforces all physical masks.

Only the stated complete rows are covered. Owner-smaller-than-whole-
cofactor rows and arbitrary partial physical/count/share masks are not
asserted paid. The theorem does not assert that every tag in an arbitrary
`V` is physically eligible.

`eventually_tagged_count_boundary` transfers the **existing** native count
payment to actual tagged incidences injectively, retaining every extra
mask in their finite set. It does not award a second count credit.

## The next signed main and its exterior boundaries

The remaining main is `sum_(p,r) D_(r,p) * sum_a w_p(a)/(Lp)`.
No native estimate by `399/5000` for that expression is proved here.

The optional continuous probe evaluates the exact old factorial selector
across the entire total-log interval `1.95N..2.03N`, keeping the product
phase. It uses finite damped-polynomial antiderivatives, with a separately
reported bound on the omitted antiderivative-series tail. It does not
include the density scalar or prove transport of any literal arithmetic
mask. The source-normalized integral can **grow transiently**: for owner
log slope `1.025`, its sampled norms are approximately `0.015` at `N=256`,
`0.71` at `N=8192` and `0.91` at `N=65536`. These are not floor units or
evidence of a cofinal bound. In particular, no claim of monotone decay is made.

The endpoint mechanism has a rigorous rate audit. `core_endpoint_rates`
proves, uniformly for the stated radius,

$$
u(39/20)e^{1/40}\le e^{-1/200000},
\qquad
u(203/100)e^{-3/200}\le e^{-1/200000}.
$$

`normalized_core_endpoint_radial` applies these to the actual successor-
order radial kernel at **both** exterior endpoints:

$$
u^{N+1}\operatorname{radial}_N(aN)
\le (N+1)ua\,e^{-N/200000},
\qquad a\in\{39/20,203/100\}.
$$

This pays endpoint radial factors, not the interior or arbitrary partial
rows. The next actual theorem must bound the signed smooth weight sum on
complete total-log windows, retain its exact owner selector and identify
which literal masks permit joining the rows. An antiderivative model
alone is not that discrete theorem.

## Optional diagnostics and scoped verification

[probe_riesz_tagged_owner_comparison.py](../scripts/probe_riesz_tagged_owner_comparison.py)
exhausts twelve toy integer rows for tags `2,3,5,7` and heights `54,65,100`.
It checks the disjoint tags, exact sieve subtraction, head cancellation,
two Riesz hinges and all-count sum. The toys **fail** `exp(N/2)<=M` and
the original core window. The geometric theorem is not applied to them.
The eighteen continuous cases are also diagnostics, with floating logs,
phases and coefficients, not interval certificates or native floor points.
Both probes are optional and absent from builds and CI.

The [local audit](riesz-tagged-owner-comparison-audit.json) records strict
Lean/build, namespace lint and standard transitive axioms using the compiled
ordinary root plus this explicit leaf. Earlier proof/audit snapshots are
preserved. No root-source rebuild, wider gates, README/explorer changes,
commit or push is included. No numerical floor, ceiling, zero exclusion
or RH proof is claimed.
