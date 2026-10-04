# Saddle-matched two-center test

The new experiment changes the evaluation ordinates while keeping one
finite prime mask and every factorial order fixed. The vertical comparison
lowers the **selected source model**, but no independent arithmetic floor
has been obtained. Its exact signed comparison cost remains unpaid.

The baseline is `48f975c2154fe65919f66218dab86a42ec78aa99`, with the local
fixed-cutoff audit preserved. This work is local, unregistered in the ordinary
root, and does not change any public zero-free or RH claim.

## Which comparison was tested

Let `s0=3/2+i*y`, `u=3/2-beta`, and retain the original `N`, moving length
`L_N`, factorial endpoint `K0=13*N/32`, and prime mask. Set

$$
\delta_N=\frac{3}{100\sqrt{N+1}},\qquad
s_\pm=s_0\pm i\delta_N,\qquad
\theta_N=\arg(u+i\delta_N)=\arctan(\delta_N/u).
$$

The factorial kernel of order `i` at the plus center is multiplied by
`exp(i*theta_N*i)`; the minus center has the opposite factor. Both swapped
incidences are averaged. This is exact selected-pole phase matching, and
asymptotically factorial-saddle matching: `theta_N/delta_N -> 1/u`.
It is not the earlier `s0 -> s0+1` pole killer or a cutoff repartition.

For `x=log p`, `z=log q`, the checked same-mask identity is

$$
\frac{\widetilde K_i^+(p)\widetilde K_j^-(q)
      +\widetilde K_i^-(p)\widetilde K_j^+(q)}2
=\cos\!\bigl(\theta_N(i-j)-\delta_N(x-z)\bigr)
  K_i(s_0,p)K_j(s_0,q).
$$

`ZetaRieszSaddleCenters.pair_eq_cos_mul` retains the entire old product
phase. It holds for arbitrary finite masks, repeated primes, and zero
factorial orders. `same_mask_ledger` gives exactly

$$
\text{original sum}=\text{two-center comparison}+\text{signed curvature},
$$

where the curvature uses the multiplier
`1-cos(theta_N*(i-j)-delta_N*(log p-log q))` on the old complex atom.
That scalar is nonnegative. The complete real contribution need not be.

The analogous real-center comparison, normalized by
`exp(shift*i/u)`, has the exact multiplier

$$
\cosh\!\left(\text{shift}
\left[\frac{i-j}{u}-(\log p-\log q)\right]\right)\ge1.
$$

Thus real saddle matching supplies no pointwise absolute-amplitude saving.
This does not rule out a future signed real-center inequality.

## Selected-source computation

At the selected pole, the logged prime moment of order `k` has principal
part `-m/(u +/- i*delta_N)^(k+1)`. After exact angular normalization, each
leg is

$$
-m r_N^{k+1},\qquad
r_N=\left(1+\frac{(3/(100u))^2}{N+1}\right)^{-1/2}.
$$

Lean proves this pole algebra exactly, with every low order retained. It
also proves the complete finite constant/geometric-array evaluation:

$$
H^{\rm model}_{N,K}
=m^2r_N^{N+1}\left[
1+H_{N-K}-H_K
-r_N\frac{N+1}{uL_N}(H_{N+1}-H_K)\right].
$$

Here the `H_j` on the right are harmonic numbers. The integer-floor
definition of `L_N` and the original factorial endpoint remain exact.

Consequently, with `S0(u)=1-c_ret(u)`,

$$
H^{\rm model}_{N,K_0}\longrightarrow
m^2 f(u)S_0(u),\qquad
f(u)=\exp\left(-\frac{(3/100)^2}{2u^2}\right).
$$

The model difference from the old evaluator tends to
`m^2*(1-f(u))*S0(u)`, not zero. Lean proves uniformly on the original strip

$$
f(u)S_0(u)<\frac{399}{5000},\qquad
(1-f(u))S_0(u)>\frac1{7000}.
$$

The first inequality is for unit multiplicity. Every quadratic model
quantity scales by `m^2`. It is not an independent upper bound on actual
primes, even under a hypothetical exposed zero.

Rounded 360-bit scalar controls, independently replayed at 420 bits:

| u | Original S0 | Two-center model f S0 | Signed difference | Headroom below 0.0798 |
|---|---:|---:|---:|---:|
| 0.5 | 0.079929339846 | 0.079785596442 | 0.000143743404 | 0.000014403558 |
| 0.500025 | 0.079900571421 | 0.079756894109 | 0.000143677312 | 0.000043105891 |
| 0.50005 | 0.079871797035 | 0.079728185813 | 0.000143611222 | 0.000071814187 |

For a simple source, using this candidate would still require controlling
the signed difference to about 10% of its model mass near `u=1/2`, or 50%
at the ceiling. The damping itself earns none of that arithmetic credit.

## Literal prime-density saddle: a different large-order regime

The absolute prime-density saddle is `T=2N`, whereas the selected-zero
saddle is `T=N/u`. They agree at `u=1/2`, but differ for every `u>1/2`.
The optional `probe_riesz_physical_saddle.py` therefore also tests the
literal saddle normalization `theta_N=2*delta_N`, rather than the exact
selected-pole phase normalization above.

The remaining selected-leg phase is

$$
\psi_N=2\delta_N-\arctan(\delta_N/u),\qquad
\frac{\psi_N}{\delta_N}\to2-\frac1u>0.
$$

Lean proves both this limit and `(N+1)*psi_N -> +infinity` for fixed
`u>1/2`, `eta>0`. A small individual center displacement is consequently
not a small accumulated factorial phase. At the ceiling and `eta=0.03`,
the first order-one accumulated phase occurs around `N=2.8*10^10`.

The floating source-model scan, with 75/110-digit agreement, finds:

| u | N | Literal-saddle model response |
|---|---:|---:|
| 0.5 | 10^16 | 0.079785596442 |
| 0.50005 | 10^10 | 0.069986757479 |
| 0.50005 | 10^12 | 0.026839176393 |
| 0.50005 | 10^14 | -0.006366845537 |
| 0.50005 | 10^16 | -0.000238599235 |

Here the factorial sums are joined before approximation. The moderate
orders are also directly summed. At huge orders the script uses sine/cosine
integrals for the two smooth harmonic prefixes and records the elementary
right-endpoint-rule error formula; the latter is about `1.6*10^-13` in the
last row. The moving-floor length replacement has its separate error bound
recorded. These **floating model rows are not interval-certified** or Lean
packet estimates. They indicate delayed order cancellation, not an earned
arithmetic saving. The model becomes qualitatively different only at orders
far beyond ordinary exploratory scans, and this behavior is nonuniform as
`u -> 1/2`.

The original-minus-comparison cost must still be kept. Making the compared
model small transfers the old selected mass to that cost unless a new
independent signed inequality controls it. No such inequality is proved.
The scan is worth preserving as a more precise new-data test, rather than
closing the whole two-center route from moderate-order observations alone.

## What is proved for the actual carrier

`ordinaryLeg` defines the genuine complete ordinary-prime data at the new
ordinates. `matchedEvaluation` uses their polarized evaluator at the old
integer cutoff and length. Its exact difference from the old evaluator is
named `completedComparisonCost` and kept signed.

`norm_original_sub_joinedComparison_le` retains the established literal
carrier's old error price exactly:

$$
\left\|\text{prefixPairDefect}_N-
  (\text{matchedEvaluation}_N+\text{completedComparisonCost}_N)\right\|
\le\text{wholeCompletionBudget}_N+\text{squareBudget}_N.
$$

Only these **previously proved** errors are paid. This statement does not
identify a hard-masked two-center sum with complete-leg limits, pay a new
mask completion, or assert that the genuine moving-center cost has the
model limit. Those bridges remain separate obligations. No selected source
has been estimated to zero, and no rightmost or simple-zero existence
assumption has been added.

## Arithmetic regression and remaining test

The optional probe records 96 actual-prime factorial atoms from a preserved
finite cache, plus 16 pair responses with **all** factorial orders joined
and both original prefixes included. All prime integers are rechecked by
FLINT. The original complex phase is kept at heights 55 and 142; these
heights are not asserted zero ordinates. Both signs occur in the curvature.
The fully joined coefficient also changes the sign of the relative curvature
in some sampled boxes, so termwise attenuation cannot decide the floor.

These controls have `N=256`, below the native `N>=65536` proof regime.
They are not native-core enumeration, complete prime populations, or evidence
of a cofinal cancellation rate. The independent replay uses the uncollected
factorial components, whereas the producer uses the collected order table;
this tests the algebraic bookkeeping before any statistical interpretation.
The eight input prime pairs are pinned in
`data/riesz-saddle-centers-prime-seeds.json`; no ignored `.lake` cache is
required to reproduce this experiment.

The next useful theorem would be an **independent signed bound** for the
same-mask curvature together with its two-center comparison, after summing
orders and labels. Do not norm-pay the curvature, infer its sign from
`1-cos>=0`, or declare the changed analytic centers automatically equivalent
at source scale. The real amplitude shortcut and free-comparison-error
shortcut fail; a genuine signed two-center argument has not been refuted.

## Local validation

```sh
lake build RiemannGaussian.ZetaRieszSaddleCenters --wfail
lake env lean -DwarningAsError=true scripts/CheckRieszSaddleCenters.lean
../.venv/bin/python scripts/probe_riesz_saddle_centers.py
../.venv/bin/python scripts/replay_riesz_saddle_centers.py
../.venv/bin/python scripts/probe_riesz_physical_saddle.py
```

The optional controls passed 1,286 ball comparisons and 950 relative-width
checks. They are not Lean assumptions or ordinary CI inputs. The scoped leaf,
14 namespace linters, and complete transitive standard-axiom audit are
recorded in `riesz-saddle-centers-audit.json`. No wider checks, commits,
pushes, public metadata updates, or zero-exclusion claims are part of this slice.
The separate 21-row literal-saddle scan is explicitly floating and uncertified.
