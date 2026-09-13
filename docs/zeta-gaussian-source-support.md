# Which zeros the Gaussian source can detect

[ZetaGaussianSourceSupport](../RiemannGaussian/ZetaGaussianSourceSupport.lean)
proves the exact support of the compensated zero source. It identifies a
geometric restriction on the current argument and constructs an alternative
strip that retains any fixed hypothetical right-half zero with strictly
positive source. The previous energy and budget decay theorems remain valid;
**no additional zero exclusion or independent arithmetic bound is proved**.

## The horizontal and vertical coordinates stay coupled

Write `ell_k=line(k)`, `eta=1-ell_k+x` and `c=1+x+i*t`, with `x>0`.
For an actual nontrivial zero `rho=beta+i*gamma`, `near_iff` proves

```math
|c-\rho|<\eta
\quad\Longleftrightarrow\quad
(t-\gamma)^2 < (\beta-\ell_k)\bigl(2(1+x)-\beta-\ell_k\bigr).
```

This is an exact equivalence before either coordinate is bounded. At the
zero's own ordinate, `near_at_ordinate_iff` reduces it exactly to
`ell_k<beta`. The nearby source is defined to vanish outside this ball.
Its shifted Poisson compensation has the same cutoff.

`compensated_eq_zero_of_re_le_line` proves that every zero with
`beta<=ell_k` contributes exactly zero, for every Gaussian scale, center
shift and height. Consequently arbitrary phase frequencies cannot remove
this horizontal restriction. `sum_eq_filter_right` makes the same fact
explicit for every finite actual zero selection, preserving multiplicity.

For the current order-nine family, the fixed line is `2035/2046`.
`current_compensated_eq_zero` proves that zeros on or left of that line
are invisible to this selected source at **every dilation**. The line is
the source's visibility threshold, not a zero-free boundary. Even varying
all orders `k>=2` allowed by the current balanced-strip interface leaves
zeros with `beta<=5/7` outside its source, as proved by
`admissible_order_compensated_eq_zero`.

## Where their information went

The original complex identity retains these zeros.
`farTerm_eq_of_re_le_line` proves that their complete multiplicity-weighted
complex pole remainder is exactly the corresponding far term. The existing
near/far identity is lossless; its subsequent norm/Poisson allowance replaces
those complex contributions by a bound. Absence from the nearby source
does not establish absence from the actual zeta divisor.

This pinpoints the relevant transport choice. Changing phase coefficients
or dilating the same geometry cannot recover a zero removed by that cutoff.
A global contradiction requires a source that still detects the fixed
hypothetical zero, together with an independent bound at that source's scale.

## A height limit also moves the detector

At the current geometry `eta<=1/100`. For every finite zero window whose
ordinates satisfy `|gamma|<=H`, `bounded_window_source_eq_zero` proves
the entire source is zero whenever `|t|>=H+1`, uniformly over all `q>=1`
and all Gaussian scales. Thus, if `|t_N|` tends to infinity, every fixed
finite zero window eventually contributes **exactly zero**, even with
arbitrary moving scalar weights. This is stronger than normalized decay.

For such a fixed window, the existing source-surplus expression
`max(0,S_Z-leftBudget)^2/q^2` therefore eventually equals
`max(0,-leftBudget)^2/q^2`. Its zero limit then bounds the negative part of
the mean; it supplies no contradiction to the fixed zero. Windows that
follow moving zero ordinates are different and keep their original source
theorem, but a large-height conclusion alone leaves fixed-height zeros open.

## Consequence for the next estimate

The broader strip identity already permits coverage of every fixed
hypothetical right-half zero. With `h=beta-1/2>0`, choose

```math
\sigma=1+\frac h4,\qquad \eta=\frac12-\frac h4,
\qquad \sigma-\eta=\frac12+\frac h2,
\qquad \sigma+\eta=\frac32.
```

`fixed_zero_geometry` proves the required strip conditions and that the
zero lies strictly inside the source ball at its own ordinate. This uses
the existing growth domain and needs no extension of its right boundary.
`compensated_pos_at_ordinate` proves the aligned compensated source
strictly positive at every positive Gaussian scale, keeping the actual
multiplicity. The strict margin follows from that zero's own shifted
Poisson reserve and the existing complete Gaussian source lower bound.
This positivity theorem applies to every eligible aligned strip; the
displayed geometry supplies one explicit witness for each `beta>1/2`.

`exists_fixed_zero_source_constraint` discharges this geometry in the
original Gaussian strip inequality. For every `B>0` and finite `M>=0`,
it retains the selected positive source, original prime sum, both signed
boundary means, complex pole/completion correction and full shifted xi
response. It assumes a hypothetical zero with `beta>1/2`; it does not assert
one exists. **The independent source-beating budget comparison is open.**
The fixed-order-nine energy and correction decay theorems have different
geometry and limit hypotheses; they cannot be transferred without proof.

The [signed-budget reduction](zeta-gaussian-signed-budget-reduction.md)
still gives a concrete left-mean target for boundary-region improvements.
For the global RH goal, test every proposed limit for retention of a fixed
zero before investing in further normalized decay. The
[centered prime carrier](signed-prime-carrier-information-audit-2026-09-12.md)
already preserves its fixed-zero multiplicity as a nonzero limiting source.
Its independent cofinal signed floor remains open. The adaptive strip above
provides another valid source, with its full signed arithmetic estimate
still required. Restoring complex far terms remains a possible alternative.

The root imports the module and the explorer's **Source visibility** endpoint
links its support, far-remainder, moving-height and adaptive-source theorems. All work remains
local under the user's no-commit instruction.
