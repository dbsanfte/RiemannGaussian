# Native square payment and the remaining odd-core covariance

2026-10-19. Local continuation of the
[all-square arithmetic checkpoint](arithmetic-operator-all-square-finite-gates.md).
The square-sector bound now reaches the original normalized central tuple
family. The complementary odd-core signed estimate is still open.

## New checked payment

[`QuasiRHSquareNativePayment`](../scripts/QuasiRHSquareNativePayment.lean)
proves, on the existing native central spectral window,

```text
norm(original normalized square integral for one unselected tuple)
  <= C * (1 + norm(t))^degree * Z^(5/72 + 255*epsilon) * L^(-1/6),

norm(sum of the original weighted unselected tuples)
  <= C * (1 + norm(t))^degree * Z^(5/72 + 255*epsilon).
```

The first theorem is `native_square_tuple`; the second is
`native_square_joined`. The multiplier is the original complex
`sqrt(Q)^(-1)/(2*pi)`, included exactly once. The companion is the literal
`lowSelectedInverseRow`: all selected prime marks, completed cube powers,
ray/calibration data, phases and support conditions remain. There is no
assumed energy estimate or unidentified companion norm in either conclusion.

The proof composes the unconditional original-amplitude theorem with the
imported normalized companion estimate. Their small exponent costs add to
`254.5*epsilon`, rounded upwards to `255*epsilon`. The exact unselected
tuple payment uses `theta=-1/6`, hence the summable exponent `-5/3`, with
no extra count of tuples. The calibration and all fixed profile constants
stay fixed before the limit in `Z`.

The leading exponent improves the old `3/16` norm cost by `17/144` on
this population. This is a genuine arithmetic payment for the specified
central-window sum. The remaining common Gaussian integration and source
normalizer are separate interfaces, with their stated losses. No bound
for a square-filtered remote family follows from the whole remote bound.

The source ledger remains

```text
Probe - F_all
  = centralSquare + (centralOdd - F_all) + remoteAll.
```

No hypothetical-zero source is assigned to the square subset. The whole
odd-core contribution must still be estimated jointly with its prescribed
companion and `F_all`.

## Exact odd-core resonance audit

This part is a paper-level applicability audit with exact finite regression
checks, rather than a new Lean theorem.

For a squarefree physical column `b`, spectral index `I*J^3` with `I`
squarefree, and numerator `zeta*r*x^2` with `r` squarefree, the actual
good-prime character factor is

```text
conj(chi_b(r)) * chi_(I*J^3)(r)
  * conj(cubic_b(x)) * cubic_I(x) * 1_coprime(x,J).
```

At a good prime, put `e=v(I)`, `f=v(b)` and `j=v(J)`. Its exponents are
`e+3j-f mod 6` on `r` and `2(e-f) mod 6` on `x`. Every nonunit zero is
retained. The primitive `r` conductor is

```text
rad[(b*I/gcd(b,I)^2) * oddKernel(J)].
```

Thus the good-character principal case is exactly `b=I` and `J` square.
It still has the complete coprimality mask at `b*J`, together with the
original bad-place/calibration factors. This classification does not
identify that finite matching part with the analytic central residue
`F_all`. Such an identity, including its cutoff and contour boundaries,
has not been proved.

Complete character means do not estimate the actual incomplete,
squarefree-core, marked numerator family. The audited pairwise-completion
and triangle estimates lose the required scale. An exact off-diagonal
sixth-frequency direction can also remain coherent after fixing rays;
its source-sized overlap with the current odd-core family is unproved.
Neither its presence nor its absence is inferred from the generic norm.

## A sharper diagnosis of the norm obstruction

The revisited [Xu–Sang paper](https://arxiv.org/abs/2610.17675v1) gives a
sharp sextic norm lower bound and an all-modulus annular Gauss asymptotic.
Those analytic results are not newly imported into Lean. Its freely chosen
or positive one-ray witness is not identified with the original calibrated
physical combination or the prescribed marked companion.

Conditional on the paper asymptotic and the separately audited fixed-core
cubic bound, the critical Gauss energy persists on **large odd cores**.
Writing

```text
M = Q^(5/6) * Y^(-2/3),
H <= (Q/Y)^(4/5) * Z^(-kappa),
```

the two small-core costs divided by `M` are bounded by
`Z^(-5*kappa/6)` and a fixed constant times `Z^(-1/48)`, before the chosen
subpower losses. The native cutoff exponent is
`17/60 - 4*d/5 - kappa`, positive for every `0<=d<=1/6` if
`0<kappa<3/20`. The paper's relative errors also decay in this range.

[`QuasiRHOddCoreWitnessRateAudit`](../scripts/QuasiRHOddCoreWitnessRateAudit.lean)
checks those exact exponents, the literature length range and the
finite-energy implication: a positive total witness with these vanishing
small-core costs retains positive normalized energy outside them. Both
analytic bounds are explicit premises. This is a scoped obstruction to a
generic norm payment, not a lower bound for the actual signed detector.

The existing quadratic/cubic hybrid estimate cannot bypass the obstruction
by treating the moving cubic phase as a contraction: its two conductors
must be coprime. An exact small actual-character example also changes the
squared operator norm from `2` to `2+sqrt(3)`. This checks the failure of
that shortcut, not sharpness of the full native matrix.

## Remaining target and validation scope

The next useful estimate is a strict signed saving on the **original
central odd-core covariance**, retaining the actual spectral coefficients,
marks, cube factors and principal boundary signs. At the currently audited
lower beta endpoint, the required saving relative to `3/16` remains
greater than `13/125000` plus the other small losses. Neither a prime-core
estimate nor the already-known unmarked structured mean covers that sum.

This checkpoint keeps the imported strict `Re(s)>7/8` theorem, every
previous no-go, and the whole-source ledger unchanged. No new zero-free
region or RH result follows. Validation details, exact-probe counts,
independent review and source hashes are in the companion JSON. Only
isolated local leaves were compiled; no broad build, public registration,
commit or push was performed.
