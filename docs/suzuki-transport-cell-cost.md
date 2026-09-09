# Finite total cost in the exact Suzuki event recurrence

[SuzukiTransportCellCost.lean](../RiemannGaussian/SuzukiTransportCellCost.lean)
proves an unconditional bound for the nonlinear cost of every actual
canonical transport cell. Its complete series converges. This controls an
error in the signed recurrence; the signed arithmetic inequality required
for global positivity remains open.

## Unchanged carrier and exact identity

For index `j`, let `r_j=suzukiFirstTailChebyshevCenter j`, whose complete
prime prefix ends at `j+2`. The abbreviation
`suzukiFirstTailCanonicalGap j` is the existing `curvatureTransportGap`
with its original first-tail reset data and cutoff `j+1`. It introduces no
new choice of center, arithmetic weight, or gap.

Write `G_j` for this gap, `kappa` for `suzukiSmoothCurvature`, and

\[
a_j=\frac{\Lambda(j+3)}{\sqrt{j+3}},\qquad
I_j=a_j\bigl(\log(j+3)-r_j\bigr),\qquad
C_j=\int_{r_j}^{r_{j+1}}(s-r_j)\kappa(s)\,ds.
\]

The checked theorem `suzukiFirstTailCanonicalGap_succ` gives exactly

\[
G_{j+1}-G_j=I_j-C_j.
\]

The signed work `I_j` is retained without an absolute-value estimate.
The cell integral carries exactly the next von-Mangoldt mass, including
prime powers. Nonnegative weights make the actual centers nondecreasing.

## Independent cost bound

For any continuous density at least `c>0` on an interval, with total mass
`w`, its displacement moment from the left endpoint is at most
`w^2/(2c)`. The proof keeps both complementary first moments: the moment
from the right endpoint is at least `c*(b-a)^2/2`, and completing the
square gives the claimed bound.

Here the already proved localization
`r_j >= log(j+2)-2` and curvature estimate
`kappa(s) >= (5/6)*exp(s/2)` imply
`kappa(s) >= sqrt(j+1)/4` throughout the cell. Consequently the compiled
theorems `suzukiFirstTailTransportCellCost_bounds` and
`suzukiFirstTailTransportCellCost_le_log_sq` establish

\[
\boxed{
0\le C_j\le\frac{2a_j^2}{\sqrt{j+1}}
\le\frac{2\log^2(j+3)}{(j+1)^{3/2}}.
}
\]

The logarithmic summability theorem already developed for the eta
endpoint majorant completes the comparison. In particular,
`summable_suzukiFirstTailTransportCellCost` has no zero hypothesis or
unproved arithmetic premise.

## Uniform finite-band consequence

Let `T_S = sum' j, C_(S+j)`. The complete signed telescoping identity and
nonnegative summability give, for every start `S` and every length `m`,

\[
-T_S\le G_{S+m}-G_S-\sum_{j<m}I_{S+j}\le0,
\qquad T_S\longrightarrow0.
\]

The terminal theorem
`suzukiFirstTailCanonicalGap_block_error_uniformly_small` proves that the
absolute error is below any prescribed positive epsilon for every band
length once its starting index is sufficiently large. The theorem
`suzukiFirstTailCanonicalGap_sub_linearWork_tendsto` also identifies the
full initial-prefix correction as the negative sum of the actual costs.

These are estimates for the original canonical cells, not an exponential
surrogate or an asymptotic replacement of the Archimedean function.

## Remaining arithmetic obligation

The nonlinear cell costs cannot accumulate an unbounded loss. A global
proof still needs a lower bound for the signed work that covers the
remaining cost relative to the starting gap. Summability of `C_j` supplies
no such sign for `I_j` or its partial sums.

These local cell costs are distinct from the fixed-endpoint entropy term
`4*sqrt(N)*H(q_N)`. No summability assertion is made for that term, and the
earlier counterexample to the stronger uniform quadratic condition at
`N=5` remains unchanged. No zero exclusion or proof of RH is obtained.

Validation is local while commits are held: warnings-as-errors elaboration,
focused module/root build, declaration lint, and terminal axiom audit. This
slice has no commit, push, or new CI run.
