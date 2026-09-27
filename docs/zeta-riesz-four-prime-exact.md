# Exact four-prime debit and payment of its small-prime head

The original finite carrier now has a sharper joint inequality in
[`ZetaRieszFourPrimeExact`](../RiemannGaussian/ZetaRieszFourPrimeExact.lean)
and an independent arithmetic population estimate in
[`ZetaRieszFourPrimeHead`](../RiemannGaussian/ZetaRieszFourPrimeHead.lean).
Neither result completes a cofactor or changes the moment order, phase,
moving length, allocation or inherited support. The numerical joint
`-79/1000-o(1)` floor remains open.

The next [four/five population test](zeta-riesz-four-five-capacity.md)
adds sharp actual prime-window budgets and a proved positive five-prime
pair-balance credit. Its aggregate compensation inequality remains open.

## The adverse four-prime coefficient is exact on both phase sides

For squarefree `n` with four prime factors, put `T=log n`,
`P=largestPrime n`, and `d=L-log P`. Throughout `0<L<=T` and
`2T<=3L`, `positiveAllowance_eq` proves

\[
(\operatorname{Re}c_L(n))_+
=\frac{T}{L}\left(\log P+T-2L
 -\sum_{q\mid n,\ q\ne P}(\log q-d)_+\right)_+.
\]

The previous upper bound omitted the entire excess sum. Reflection,
largest-prime deletion and the exact three-prime clipped identity prove
the formula in every chamber, including saturation and equality cases.
Nonsquarefree coefficients and allowances are zero.

For **each** cofactor prime `q`, `positiveAllowance_le_cofactor_gap` gives
the additional bound `(T/L)*(T-L-log q)_+`. Thus, if a second prime is
reflected-large (`log q>=T-L`), the positive coefficient is zero.
`re_four_atom_nonneg_of_second_large` proves that every such original atom
has nonnegative real part whenever `cos(y*T)<=0`, without a zero hypothesis.

Combining this with the previously exact negative coefficient gives
`exactDebit`. `re_four_atom_eq_keep_positive` reconstructs the full
observed atom from its positive credit minus that exact debit, on **both**
cosine signs. `signed_floor_improves_previous` proves pointwise and finite
sum improvement. `eventually_compensated_core_floor` inserts the sharper
debit only into the untouched complement of the prior triple compensation;
it preserves both triple credits and a quarter of the one supply.

There is also a useful uniform bound for **any** marked prime `r|n`:

\[
|c_L(n)|\le \frac{T}{L}\log r.
\]

`norm_coefficient_le_marked_log` proves this without counting prime labels.
The next estimate supplies that counting step.

## A complete small-prime four-factor population is paid relatively

Fix one original radial slab `2M<=log n<=2M+2`, with moment `N<=2M`,
`M>=100`, and length `271M/200<=L<=143M/100`.
Select any actual squarefree four-prime labels with all prime logs at
most `5M/4` and some prime at most `Q`, where `log Q<=M/32`.

If two factors have logs at most `M/32` and `M/16`, respectively,
`coefficient_zero_of_two_small` proves their coefficient exactly zero.
The small composite cofactor saturates all three single-prime cutoffs;
the fourth cutoff is nonpositive. Hence every surviving label with a
marked small prime has **three** cofactor prime logs greater than `M/16`.

Actual Chebyshev bounds then count these three large primes while retaining
the marked reciprocal weight. The final small-prime budget is the already
proved `sum_(r<=Q, prime) log(r)/r <= log(4)*(1+log Q)`.
`small_four_norm_upper` proves, for the original residual atoms `f_N`,

\[
\left\|\sum_{n\in S}f_N(n)\right\|
\le B_4(1+\log Q)\frac{e^{2M}}{M+1}E(N,M),
\qquad B_4=1179648(\log4)^4e^4,
\]

where `E(N,M)=exp(-3M)*(2M)^N/N!`. This is a bound on actual prime
products, with arbitrary finite selection and real height; there is no
prime-density approximation or signed transport premise.

For `Q=N^2`, `eventually_small_four_cost` makes this an arbitrarily small
fixed fraction of `M*exp(2M)/(M+1)*E(N,M)`, uniformly across the slabs.
The relative cost is `O(log N/N)`. This does **not** assert separate
source-normalized head decay.

## One supply pays all three selected populations

`eventually_joint_slabs_spending` proves simultaneous payment by the same
actual positive four-prime supply: half for a fixed balanced triple band,
one eighth for the small-prime triples, and one eighth for the four-prime
head. Distinct radial slabs have disjoint label sets. The supply's primes
are all larger than `N^2` eventually, so it is disjoint from the new head.
The new supply credit is **not** added to an independent copy of any old one.

`eventually_core_joint_floor` applies this throughout the radial union
inside the original `coreBand`, for fixed `|y|>=16` and
`1/2<u<=10001/20000`. It proves

\[
\operatorname{Re}(u^{N+1}\mathrm{coreResponse}_N)
\ge u^{N+1}\left(\operatorname{Re}W
 +(\operatorname{Re}X)_+ +(\operatorname{Re}Z)_+
 +(\operatorname{Re}H)_+ +\tfrac14\operatorname{Re}Y\right).
\]

Here `X` is the balanced triple union, `Z` the remaining small-prime
triple union, `H=radialFours` the new four-factor head, and `Y` the one
positive supply. `W` is the complete original signed complement of those
four disjoint selections. No whole-core sign is inferred by discarding `W`.
Constants, balanced width and eventual thresholds remain existential.

`mem_radialFours_of_geometry` proves that `H` contains every original
small-prime four-factor label with
`1.952N<log n<=2.029N` and all prime shares at most `601/1000`.
The existing radial-edge and dominant-prime estimates remain available.
The displayed new floor keeps those excluded labels signed in `W`; it
does not silently delete them or add their allowances twice. The prior
full-head/triple-edge theorem also remains intact.

The remaining task is an independent bound on this signed complement
together with its retained credits, especially the rough triple and
higher-count sectors. This slice proves no zero exclusion or RH result.

## The whole exponential head is now paid

The continuation uses the same actual population estimates and the same
positive supply. `exists_log_head_budget` chooses a fixed `delta>0`, with
`delta<=1/128`, so that **every** threshold satisfying `log Q<=delta*N`
fits the two one-eighth budgets, eventually and uniformly over radial slabs.
For a desired slab budget `b`, its explicit choice is

\[
\delta=\min\left(\frac1{128},\frac{b}{8(B_3+B_4)}\right),
\qquad B_3=768(\log4)^3e^4.
\]

Here `B4` is the four-prime constant above. The final budget `b` comes from
the height-dependent positive-supply lower bound. The resulting width and
starting order are existential; no usable numerical width is certified.

Set `Q_N=floor(exp(delta*N))`.
`eventually_core_exponential_floor` enlarges both head selections to this
threshold, spending the same half plus two eighths. There is no second copy
of the supply. `eventually_polynomial_le_exponential` proves this threshold
eventually exceeds **every fixed power** of `N`.

`exists_exponential_head_missed_bound` then pays every omitted label in
the full exponential head and balanced triple band. A nonzero omitted
label must lie either on the already bounded radial edges or in the already
bounded dominant-prime sector. Its total source-normalized error is at most

\[
\varepsilon_N=C r^N+
  2\,\mathrm{majorantMass}(1+1/262144)e^{-N/1000000},
\qquad 0\le r<1.
\]

`eventually_core_full_exponential_floor` combines these results in one
inequality for the original core. Its right-hand expression retains the
three positive credits, one quarter of the same supply and the entire
signed complement, subtracting only `epsilon_N`.
`tendsto_exponential_head_allowance` proves that allowance tends to zero
on the original dyadic schedule.

Thus **all** original squarefree labels with three or four prime factors
and some `p<=exp(delta*N)` have been paid, across the full core window.
`remaining_full_head_prime_log_gt` proves every prime of a surviving
squarefree three- or four-factor label satisfies `log p>delta*N`.
The spent populations themselves are not asserted to decay separately.
Counts five and higher remain in the signed complement; the final joint
`-79/1000-o(1)` floor remains open.

## Optional numerical diagnostic

[`probe_riesz_four_prime_exact.py`](../scripts/probe_riesz_four_prime_exact.py)
records the comparison in
[`riesz-four-prime-exact-probe.json`](riesz-four-prime-exact-probe.json).
It uses the ordinary-prime-density model only at `T=2N`, sampling the
four-prime rough sector and retaining its model allocation weight.
The common radial and phase factors are omitted. The large reduction
in the positive debit motivated the proof; it does not bound the actual
arithmetic sum. Sobol repetitions and floating identity checks are not
certified quadrature. The probe stays outside ordinary CI.
