# Continuous renewal and the head-interpolation artifact

The arithmetic target remains

\[
u^{N+1}\bigl(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\bigr).
\]

**No bound for that sum, complementary floor, or zero exclusion is proved.**
This is an external numerical audit of the same synthetic modes
`0, 1/40000 +/- (3/500)i`, with multiplicities `1,3,3`. They are not
asserted to be zeta zeros. It evaluates the continuous all-count response
at fixed geometry, independently of the cutoff lattice. It does not perform
the outer radial, owner-share or beta integrations, or transport a density
to primes. All previous Lean no-go theorems remain valid.

## A continuous calculation with explicit remainder budgets

For a unit least cutoff write

\[
A(w)=\exp\left(-\sum_i m_i\int_1^\infty e^{-(w-\xi_i)x}\frac{dx}{x}\right),
\qquad B(w)=A(w)^{-1}.
\]

Each inverse consists of a unit atom at zero and an ordinary density, `a`
or `b`, supported on `t>=1`. Differentiating the count exponential and
convolving gives, for `eps=-1,+1`, respectively,

\[
f(t)=\frac{\epsilon}{t}\sum_i m_i v_i(t),\qquad
v_i(1)=e^{\xi_i},\qquad
v_i'(t)=\xi_i v_i(t)+e^{\xi_i}f(t-1).
\]

The delayed density is zero below one. This keeps every count; no individual
factorial order is removed. A common exponential tilt makes every
`Re xi_i<=0`; it is restored after computing the response.

The optional [probe](../scripts/probe_riesz_continuous_balls.py) solves this
equation on aligned cells of width `h=1/4` or `1/8`. It tracks a uniform
real-interval error separately from the midpoint Taylor coefficients:

- Initial-state errors propagate by at most one, since
  `|exp(xi_i*t)|<=1` for `t>=0`.
- A preceding-cell density error `E` contributes at most
  `h |exp(xi_i)| E` by variation of constants.
- For a polynomial forcing of degree `D`, the first omitted state
  coefficient is `c_(D+1)`. All later coefficients have successive ratios
  `xi_i/(j+1)`. The entire Taylor tail on the cell is bounded by
  `|c_(D+1)| h^(D+1)/(1-|xi_i|h/(D+2))`; the denominator is checked positive.
- Dividing the numerator polynomial by `c+x` has the exact truncation
  remainder `-f_D x^(D+1)/(c+x)`, with norm at most
  `|f_D|h^(D+1)/c`. Coefficient and evaluation rounding are added separately.

This avoids incorrectly propagating earlier errors with `exp(|Im xi|h)`.
These arguments and computations have **not** been formalized in Lean.
The reports are not kernel-checked certificates.

On `0<d<s`, the inverse ramp is

\[
F(s,d)=-d\,a(s)
 -\int_{\max(1,s-d)}^{s-1}(v-(s-d))a(v)b(s-v)\,dv.
\]

The first term retains the empty `B` atom. The empty `A` atom misses this
strict region. The code splits the integral at every density-cell boundary,
integrates the polynomial products, and pays their propagated errors before
adding the signed pieces. Rational boundary identities are kept exact.

Checks include eight closed-form density values below total log three and
an independent one-/two-cofactor calculation at `s=5/2,d=7/5`: direct subset
enumeration and a separate ball integral overlap the renewal result. A
different ODE solver with adaptive quadrature also agrees at the upper-face
moderate-order point to its floating-point accuracy; that solver's error
indicator is not used as an enclosure.

## Cutoff-grid error at fixed geometry

The [moderate-order report](riesz-continuous-balls-probe.json) uses the exact
integer-floor length, `T=(N+1)/u`, `u=10001/20000` and owner share `11/20`.
The [refinement](riesz-continuous-balls-refinement.json) halves the cell
width, raises the Taylor degree from 128 to 192 and raises precision from
768 to 1024 bits. The enclosures overlap at both points.

At `N=65536`, the continuous response is approximately:

| Least share | Continuous response |
| --- | ---: |
| `1/100` | `6.78693914322642e-28` |
| `1/25` | `-0.255004941694745` |

At the upper point, the lattice error is about `1.318e-3`, `3.298e-4`,
`8.206e-5`, and `2.060e-5` on grids 128, 256, 512 and 1024. These comparisons
are against the independently computed continuous response, not differences
between successive grids. They do not provide a uniform error bound for the
outer integral.

## Subtracting the head before interpolation can destroy cancellation

Let `I` be the existing twelve-point interpolation operator, `F` the full
signed lattice response, and `H` its one-cofactor head. The old evaluation is

\[
I(F-H)+H=I(F)+(H-I(H)).
\]

The last term is an exactly computable interpolation discrepancy. Head
cancellation in the exact joined integral does not make this discrepancy
zero. When the count sum has already made `F` tiny, replacing its small
node values by the large `F-H` values can introduce an artificial response.

The [million-order report](riesz-head-interpolation-probe.json) evaluates
`N=1048576`, owner share `11/20`, and least share `1/99` (near the lower
factorial face). The continuous response is about
`5.952610230868735e-19`; its one-cofactor head is about `2.77e10`.
A separate [refinement](riesz-head-interpolation-refinement.json), using
cells of width `1/8` and degree 512 instead of `1/4` and 768, agrees.

| Grid | Interpolate the intact signed response | Split and restore the head |
| ---: | ---: | ---: |
| 128 | `5.38499e-19` | `847532.585` |
| 256 | `5.82322e-19` | `201.170245` |
| 512 | `5.92099e-19` | `0.07904399` |
| 1024 | `5.94475e-19` | `1.18344e-5` |
| 2048 | `5.95065e-19` | `4.72880e-9` |

Every difference between the two columns agrees with the independently
evaluated `H-I(H)`. Tiny arithmetic rounding balls cannot remove this error.
This diagnoses a fixed-point numerical artifact, not the size or sign of
the integrated artifact and not a counterexample to an arithmetic theorem.

**Next use:** evaluate the continuous count sum before the outer quadrature,
or use an interpolation whose error is controlled for the entire signed
response. Do not take the old split-head million-order outputs as evidence
of a surviving source. Nor infer decay from these tiny fixed-point values:
the two weighted boundaries, radial integral, mode assignments and literal
prime measure still have to be controlled together.

The subsequent [coupled audit](zeta-riesz-coupled-continuous-audit.md)
uses this continuous response before the outer quadrature and separately
checks radial phase error. It also retains a large upper-boundary response
at the million-order fixed point. Neither tiny lower-boundary values nor
small rounding balls settle the joined sum.

## Reproduction

Run outside ordinary CI and certificate verification:

```sh
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_continuous_balls.py \
  --order 65536 --shares 1/100 1/25 --subdivision 4 --degree 128 --bits 768 \
  --grids 128 256 512 1024 --output /tmp/riesz-continuous.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_continuous_balls.py \
  --order 1048576 --shares 1/99 --subdivision 4 --degree 768 --bits 2048 \
  --grids 128 256 512 1024 2048 --output /tmp/riesz-head-interpolation.json
```

The probe rejects non-finite or overly wide response balls, checks its
source hashes before and after computation, and retains the exact length
and complete one-cofactor head in the report. The hard count caps happen to
exceed all available counts at these fixed geometries; this observation is
not a uniform count-mask transfer for the full packet.
