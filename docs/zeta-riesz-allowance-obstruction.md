# The improved positive allowance cannot close the contradiction

The requested fixed target is too large. Lean proves, with the existing
definitions unchanged,

$$
B_j(u,y)-B_{4,j}(u,y)
\ge c(u,y)\,\frac{(2u)^{N_j}}{(N_j+1)^4}
\longrightarrow +\infty,\qquad c(u,y)>0,
$$

for every fixed real height `y` and every `1/2 < u <= exp(-11/16)`.
Here `N_j` is the original `dyadicMomentOrder j`. Consequently

$$
B_j-\frac34 B_{4,j}
= (B_j-B_{4,j})+\frac14B_{4,j}
\longrightarrow +\infty.
$$

Theorems in
[`ZetaRieszAllowanceGrowth.lean`](../RiemannGaussian/ZetaRieszAllowanceGrowth.lean):

- `eventually_complement_growth`: the positive exponential lower bound.
- `complement_tendsto_atTop`: divergence of the exact complement.
- `improved_allowance_tendsto_atTop`: divergence of the fixed target.
- `not_frequently_improved_allowance_le_three_fortieths`: no cofinal
  subsequence can satisfy the requested `3/40` ceiling.

No hypothetical zero, exposure, simplicity or unproved prime-density
premise is used. The positive constant and starting index are not
numerically evaluated. Uniformity in an arbitrary moving height is not
asserted.

## The surviving complement

The lower bound comes entirely from actual squarefree integers `n=pqr`,
with three distinct primes in consecutive, disjoint logarithmic intervals
near `2N/3`. Their products have `log n = 2N + O_y(1)`.

| Restriction | Why this subfamily survives |
| --- | --- |
| Window `7N/4 < log n <= 9N/4` | The bounded displacement from `2N` fits eventually. |
| Count `3 <= omega(n) < K_j` | Exactly three distinct factors; `K_j >= 4`. |
| Earlier original masks | `window_mem_originalMask` discharges all masks using the actual cutoff. |
| Physical cutoff | Each prime has at most half the product logarithm, below the physical length. |
| Paid allocation sectors | Balanced factors have `log p <= (log n)/2`, below both dominant thresholds. |
| Unassigned fraction | `theta <= 3 exp(-N/64)` implies `1-theta >= 1/2` eventually. |
| Original product phase | A bounded shift gives `cos(y log n) >= 1/2` on the whole box. |
| Four-prime credit | Exactly absent: `omega(n)=3`. |

The [support audit](../RiemannGaussian/ZetaRieszAllowanceComplement.lean)
proves the inclusion and surviving weight. The
[prime-box proof](../RiemannGaussian/ZetaRieszAllowancePrimeBoxes.lean)
proves unique product counting and derives the number of actual primes
from the repository's unconditional prime number theorem. The boxes supply
at least a positive multiple of `exp(2N)/(N+1)^3` distinct integers.
Their original factorial weights and Stirling's inequality give the
displayed source-scale lower bound.

## Consequence for the signed campaign

The finite inequality `Re R_j >= -B_j + (3/4) B_4,j` remains true, but
provides no bounded lower floor. A fixed-factor saving cannot remove the
exponential contribution from this complement. Further divisor-sign
calculations do not change the fixed positive target, which already uses
absolute cosines.

The evaluated source limit for the signed remainder is unchanged. Large
positive and negative contributions can cancel inside that sum. An
independent estimate must retain enough of that cancellation to beat the
`3/40` source deficit. This audit gives no restricted zero exclusion or new
zero-free region; it corrects the proposed endgame target.

The [allowance obstruction explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=allowance-obstruction)
exposes the checked lower bound, divergence and no-cofinal-ceiling theorem.
The main explorer continues to end at the signed source with its open floor.

The subsequent [signed symmetric completion audit](zeta-riesz-symmetric-completion-audit.md)
checks the Newton/Euler differential operators and the truncated
Selberg–Vaughan identity. It identifies an additional pair-cutoff correction
on these very same surviving triples; no independent signed floor is yet
proved by that completion.
