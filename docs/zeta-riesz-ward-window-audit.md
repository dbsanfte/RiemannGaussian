# The matched logarithmic slope does not by itself pay the order window

The preceding arithmetic results pay the marked prime-range mismatch and
the unshifted cofactor branch. Neither estimates the remaining reflected
profile or the full matched Euler response. This audit tests a specific
shortcut: whether matching a quotient to its own logarithmic derivative
forces cancellation inside the existing factorial rectangle.

[`ZetaRieszWardWindowAudit`](../RiemannGaussian/ZetaRieszWardWindowAudit.lean)
proves that it does not. It also identifies the different behavior of a
simple zero. These are normalized analytic models **before Fourier
integration**, not models of the actual prime population.

Write `M_k` for the existing signed factorial Taylor moment at zero. Keep
the literal `rectangleOrders`, its `ownerOrders` constraint, the correlated
cofactor order `N+1-j-h`, and the reciprocal marked weight:

\[
 B_N(F,a)=\sum_{j,h\text{ in the original rectangle}}
 \frac{M_{j-1}(-F'/F)}{j}\,a_h\,M_{N+1-j-h}(F).
\]

For `N>=4`, Lean proves every selected cofactor order at least two.
Consequently `B_N(1+s,a)=0` for **every** low-leg sequence `a`, including
all retained low orders. This is exact finite annihilation for the
simple-zero cofactor; it does not infer a masked arithmetic limit from
complete-leg limits.

In contrast, take `F(s)=1/(1+s)`. Lean proves exactly `-F'/F=F` near the
center and `M_k(F)=1`. With the fixed reciprocal low leg `a_h=1/(h+1)`,

\[
 B_N(F,a)=\sum_{j,h\text{ in the original rectangle}}\frac1{j(h+1)}.
\]

At every order `N=400t`, `t>=1`, the subrectangle
`210t<=j<=230t`, `4t<=h<=12t-1` is contained in the original mask. Counting
its terms and bounding their denominators proves

\[
 \boxed{\quad |B_{400t}(F,a)|\ge\frac1{20}.\quad}
\]

`not_tendsto_pole_rectangle_norm` therefore rules out a generic decay
conclusion from the matched-slope identity and this rectangle alone.
No analytic continuation, zero assumption or numerical trust enters.

## Optional quantitative test

[`probe_riesz_ward_window.py`](../scripts/probe_riesz_ward_window.py)
checks the exact integer window and evaluates two positive pole models:
the reciprocal low leg and a Poisson factorial leg with mean `N/40`.
The latter depends on `N` and is an additional diagnostic only. At order
262144 their values are approximately `0.126108` and `0.090971`.
The respective predicted limits are `log(23/21)*log(4)` and `log(23/21)`;
those limit formulas are **not** Lean theorems in this slice. The independent
Lean lower bound is sufficient for the no-go.

Run outside ordinary CI:

```sh
python3 scripts/probe_riesz_ward_window.py \
  --output docs/riesz-ward-window-probe.json
```

## A positive test for the joined time profile

The same probe also keeps both frequency shifts in a height-zero pole
model, with `c=1/2`, `k=N+1-j-h`, and symbol

\[
 \frac{c^{-j}-(c+i\xi)^{-j}}{j}
 \frac{c^{-h}-(c+i\xi)^{-h}}{h}
 \frac{i\xi}{c^{k+1}}.
\]

Its proposed Fourier inverse is a joined integer-gamma expression.
Define the finite Poisson prefix

\[
 Q_m(x)=e^{-x}\sum_{v=0}^{m}\frac{x^v}{v!},\qquad
 D_{j,h}(x)=Q_{j+h-1}(x)-Q_{j-1}(x)-Q_{h-1}(x).
\]

The scalar tail bound is now proved in Lean. The literal rectangle implies
`200*(j+h)<=123*N`. With `x=L/2>=11N/16`, the rational tilt `9/10` gives

\[
 Q_m(x)\le(10/9)^m e^{-x/10}\le e^{-N/300}
 \quad(200m\le123N).
\]

`poissonPrefix_rectangle_bound` uses the proved rational enclosure
`log(10/9)<=53/500`; it does not trust a numerical normal approximation.
`joinedPoleTail_bound` retains the three signed tails and proves their
absolute value at most `3*exp(-N/300)`. Finally,
`source_joinedRectangleTail_bound` sums the **whole exact order rectangle**
with both reciprocal weights and pays the positive source growth:

\[
 \boxed{\quad
 \left|(2U)^N\sum_{j,h}\frac{D_{j,h}(L/2)}{jh}\right|
 \le3(N+2)^2e^{-N/400},\qquad U=10001/20000.
 \quad}
\]

This is a proved estimate for the scalar model, not a theorem identifying
it with the literal ordered-prime response. In particular, the proposed
Fourier inversion is not formalized here. The pole model extended to all
frequencies has a `1/xi` integrand tail; its inversion needs an improper
or Abel-regularized interpretation. The actual finite Euler integrand has
the separately proved absolute integrability. Equating those two objects
requires a justified comparison, including the exterior frequency terms.

The optional probe uses the **actual integer-floor length**
`2*log(floor(U^(-N)/(N+1))+2)`, and evaluates the normalized scalar model
with its full prefactor. It gives approximately:

| Order | Joined gamma-model response |
| --- | ---: |
| 400 | `1.16118e-3` |
| 640 | `1.55397e-4` |
| 1600 | `2.91168e-7` |
| 6400 | `5.32915e-18` |
| 25600 | `1.06415e-56` |

The tail theorem's length premise is false at the first two displayed
orders and true at the last three; the JSON records this. These are
binary64 model evaluations, not certified prime values. They locate a
possible joint-frequency mechanism, rather than paying the missing
arithmetic transfer.

With `--fourier-check`, the optional probe independently evaluates the
improper oscillatory integral at two test points using SciPy. It agrees
with the gamma formula within `3e-15`; QUADPACK's estimated errors are about
`1.2e-11`. This checks the proposed sign and normalization numerically.
It is not an interval certificate or a Lean Fourier-inversion theorem.

## Consequence for the actual proof

Matching the actual high mark to its own ordered Euler quotient remains
valid and useful; all paid error bounds remain intact. The audit does not
show that the actual prime packet grows, nor that its joint Fourier integral
fails to cancel. The synthetic reciprocal low leg is not substituted into
the carrier. In particular, this is not a new masked-mode obstruction to
the full coupled arithmetic target.

The next estimate must use the extra information absent from the shortcut:
the specific ordered Euler quotient and the cancellation between its two
shifted frequencies under the moving-length Fourier integral. The generic
unmasked Ward identity, or the fact that the prime ranges now match, cannot
replace that estimate. The reflected signed main and the complementary
carrier's independent one-sided floor both remain open.
