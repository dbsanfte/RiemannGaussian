# Second-reflection savings in both whole Riesz bounds

Both actual whole-sum comparisons now use sharper signed six-prime costs
on their unpaid remainder. Every previous population payment, favorable
observation, original mask and factorial allocation is preserved. This is
an independent arithmetic inequality; it assumes no zero or simplicity.
The final numerical whole floor and ceiling remain open.

## The coefficient being bounded

For a squarefree six-prime label `n`, put `T=log n`, `D=T-L`. Suppose
exactly one prime has logarithm at least `D`, and let `a` be the product of
the remaining five actual primes. The original coefficient satisfies

```math
c_L(n)=-\frac TL\,\mathcal R_D(a)
       =\frac TL\,\mathcal R_E(a),\qquad E=\log a-D.
```

The second equality uses the odd parity of the five-prime cofactor. The
full integer `n`, its complex phase and its allocation factor do not
change. At cutoff `E`, primes of `a` with log at least `E` cannot enter any
contributing divisor. Let `b` be the product of the remaining active
primes, and let `o` be the number removed at this second cutoff. Then

```math
c_L(n)=\frac TL\,\mathcal R_E(b).
```

For `o<=3`, `b` has exactly `5-o` distinct prime factors and has the same
least prime as `n`. The already-proved signed divisor bounds give:

| Second-cutoff removals | Old coefficient interval | New interval |
| ---: | ---: | ---: |
| 1 | `[-3,3]` | `[-2,1]` |
| 2 | `[-3,3]` | `[-1,1]` |
| 3 | `[-3,3]` | `[0,1]` |

All entries are in units `(T/L)*log(minFac n)`. For `o=1`, the new lower
endpoint improves from `-2` to `-1` when `3E<=log b` or `2 log b<=3E`.
The last row is actual arithmetic nonnegativity, not a numerical sign
prediction. Unhandled inner counts keep their old proved bound.

## Phase and midpoint information both survive

The preceding midpoint estimate is retained:

```math
C(n)=\frac TL\min\{3\log p_{\min},\,4|2D-\log a|\}.
```

Let `A_-` and `A_+` be the minima of `C(n)` with the new negative and
positive allowances. With `x=y log n`, the directed costs are

```math
D_-(n)=A_-(n)[\cos x]_+ + A_+(n)[-\cos x]_+,
\qquad
D_+(n)=A_+(n)[\cos x]_+ + A_-(n)[-\cos x]_+.
```

Lean proves both costs nonnegative and no larger than the earlier centered
cost on the same literal label. For the original residual atom `v_n`, with
its nonnegative original weight `w_n`,

```math
[\Re v_n]_+-w_nD_-(n)\le\Re v_n
\le\min\{\Re v_n,0\}+w_nD_+(n).
```

No absolute value of the whole carrier replaces either signed sum.

## Actual whole-sum application

The optional checked whole floor and ceiling retain exactly

```math
E_N=S\setminus(P\cup I\cup H\cup Q\cup D),\qquad
M_N=\left(\frac2{25}\sqrt{N+1}-\frac18\right)G_N.
```

The new six-prime costs are applied only inside `E_N`; all other labels
remain signed. All three numerical cover assemblies were already checked,
so neither application assumes a new cover, density estimate or surplus.
The margin, population witnesses and vanishing error are unchanged.
The new directed costs only improve the existing two comparisons.

Other six-prime configurations, other counts and other radial periods still
require a signed population estimate. The cofinal whole `-79/1000-o(1)`
floor and `3/2+o(1)` ceiling have not been proved. Exposure does not imply
simplicity, and this result is not a zero exclusion.

## Quantitative diagnostic

The existing reproducible angular probe, at `L/T=0.6931`, gives these
approximate one-large coefficient allowances:

| Allowance | Sampled angular integral |
| --- | ---: |
| Previous symmetric centered allowance | 0.60596 |
| New negative allowance | 0.38383 |
| New positive allowance | 0.36204 |

The same samples give actual positive and negative coefficient masses of
about `0.04613` and `0.07154`. The remaining difference shows why even the
new pointwise bounds do not settle the signed population estimate.
These numbers exclude the radial and phase factors and majorize the old
unassigned fraction by one. They are not rigorous enclosures, literal prime
counts, or costs spent in the whole inequality. The Lean proof is independent
of this experiment.

## Proofs and checks

- [Signed arithmetic intervals, clipping and exact core subset bounds](../RiemannGaussian/ZetaRieszSixPrimeSecondReflection.lean).
- [Concrete whole floor and ceiling](../scripts/CheckRieszSixSecondWhole.lean).
- [Prior combined population ledger](zeta-riesz-combined-triple-payment.md).
- [Certificate and theorem audit](riesz-central-capacity-audit.json).
- [Angular diagnostic](riesz-six-remainder-probe.json) and
  [reproduction script](../scripts/probe_riesz_six_remainder.py).

After the cached assemblies and combined triple application have passed,
use the same optional Lean import path documented in the combined ledger:

```sh
"$riesz_lean" -DwarningAsError=true --root="$PWD/scripts" -o .lake/riesz-positive-five-application/CheckRieszSixSecondWhole.olean scripts/CheckRieszSixSecondWhole.lean
```

The application prints both terminal axiom sets and runs declaration lint.
No exhaustive cover is added to the ordinary build or CI.
