# Correlated owner integration and remaining numerical errors

**External numerical audit only. No new Lean theorem, retained signed
prime-sum bound, source asymptotic or zero exclusion is claimed.** The
arithmetic target remains the original joined counts 3–55 / 3–13 with
every mask and both least-order boundaries.

The [collected report](riesz-owner-integration-probe.json) records input
hashes, independent checks and error budgets. These optional probes stay
outside ordinary CI and the numerical-certificate workflow.

## Why the larger test needs different integration

At `N=262144`, the old 48-node beta rule misses the tested twelfth-harmonic
moment by about `0.86026`. The 160-node rule has error below `1.1e-31` for
that same moment, against an independent ball reference. For a radial
exponential test with frequency `3/500` and growth `1/40000`, the gamma
rules give errors about `0.002442` at 32 nodes and `4.36e-16` at 48 nodes.
These are errors for individual exponential moments, not the full response.

The new conditional-owner rule incorporates the exact positive measure

\[
d\nu(x)=\frac{B_{M,l,h}(x)}x\,dx,\qquad
B_{M,l,h}(x)=\sum_{j=l}^{h}\binom Mj x^j(1-x)^{M-j},
\qquad p=(1-r)x.
\]

Its zeroth moment is `sum (1/j)`. For positive integer `k`, its moment is

\[
\int_0^1 x^k\,d\nu(x)=
\frac{(k-1)!M!}{(M+k)!}
\left[\binom{h+k}{k}-\binom{l+k-1}{k}\right].
\]

The computed recurrence uses midpoint coefficients. It is an approximate
positive rule, **not an asserted exact Gaussian rule**. The numerical
audit charges both value and derivative interpolation defects. At the
upper face and the conservative frequency `6385.82784`, its pure-Fourier
Hermite bound is about `2.74e19` at 128 nodes and `9.91e-26` at 192 nodes.
This does not control a varying amplitude or a hard mask. No owner
marginal is fitted or calibrated; the relation `p=(1-r)x` remains exact.

## Integrating the complete varying response

For fixed radial variable `T` and least share `r`, put
`lambda=L_N/T`, `s=(1-p)/r`, `d=(lambda-p)/r`, and `g=s-d`.
The already-audited continuum response, including the empty-cofactor
boundary, is

\[
\mathcal R(s,s-g)=-(s-g)a(s)
 -\int_g^{s-1}(v-g)a(v)b(s-v)\,dv.
\]

Here `a` and `b` are the signed and unsigned renewal densities. The
model retains the three conjugation-symmetric tilted modes
`-Tr/40000`, `+3iTr/500`, `-3iTr/500`, with multiplicities `1,3,3`.
They are synthetic modes, not asserted zeta zeros or sampled primes.

The new [spline projector](../scripts/riesz_response_spline.py) convolves
the complete density polynomials before taking a norm. At each physical
cell it keeps a separate uniform density error. Polynomial extension
jumps use the exact identity

\[
(x_+^i*x_+^j)(s)=\frac{i!j!}{(i+j+1)!}s_+^{i+j+1}.
\]

The [local moment helper](../scripts/riesz_owner_moments.py) then integrates
each polynomial against the original conditional factorial band. It uses
the Pearson equation for the two beta densities whose difference is
`B'`. Both interval boundary terms are retained. Explicit division and
exponential Taylor remainders pay the nonpolynomial factors; only those
remainders receive absolute values. The physical mask `1/2<p<3/5` is
the integration domain, not an uncharged deletion.

Thus the [owner-integral probe](../scripts/probe_riesz_owner_integral.py)
encloses the entire signed integral

\[
\int_{1/2}^{3/5}\frac{B_{M,l,h}(p/(1-r))}{p\lambda}
\left[e^{T(1-p)/40000}+6e^{T/40000}\cos(3Tp/500)\right]
\mathcal R\!\left(\frac{1-p}r,\frac{\lambda-p}r\right)dp.
\]

At the radial mean `T=(N+1)/u`, `u=10001/20000`, and the exact beta mean
`r=(h+1)/(N+2)` of each indicated face, the results are:

| N | Face | Signed owner integral, approximately | Explicit density/Taylor budget |
|---:|:---|---:|---:|
| 65536 | Upper | `0.31308738582293044` | `<3.7e-55` |
| 262144 | Upper | `-12783.431344252788` | `<2e-46` |
| 262144 | Lower | `2.5324275871135781e-24` | `<5.8e-69` |

Increasing the second calculation from degree/order 192 to 224 gives an
overlapping enclosure with explicit budget below `1.6e-60`. The report
also includes roundoff and display rounding. Its 256-node owner-rule
comparison differs from the enclosed integral by about `6.88e-9`.
This illustrates why the pure-Fourier bound is not a full-integrand bound.

The lower-face calculation uses degree 224, Taylor order 192 and 8192-bit
arithmetic. It integrates 81 owner intervals and passes 243 independent
local-convolution comparisons. Its small value is a fixed-geometry result;
it does not yet bound the full lower face.

All three calculations retain every geometrically possible count at those
fixed points: the beyond-cap count allowance is zero there. They do not
pay count tails at other least shares. Each spline is checked at three
interior points per interval against the independent local convolution.
There are also 39 exact rational band-moment checks, three independent
beta-function references, and an independent complex quadrature for a
small polynomial/phase example with the same division and weights.

**The displayed point integrals are not the coupled response. Their
size and sign do not establish growth, decay, a source coefficient or an
arithmetic floor. Radial and least-share oscillations remain coupled.**

## The one-cofactor head cancels in the joined model

The conditional beta/binomial marginal obeys

\[
\int_0^{1-p}\frac{(N+1)!}{h!(N-h)!}
r^h(1-r)^{N-h}
\binom{N-h}{j}\left(\frac p{1-r}\right)^j
\left(1-\frac p{1-r}\right)^{N-h-j}dr
=\binom{N+1}{j}p^j(1-p)^{N+1-j}.
\]

It is independent of the least order `h`. Consequently the
cutoff-independent one-cofactor head cancels between faces, with the
same physical owner mask and radial integration. This is the numerical
analogue of the existing joined-head cancellation audit; it is not a
coefficient formula for a prime cofactor in the literal arithmetic sum.

The new [head audit](../scripts/probe_riesz_owner_head.py) evaluates its
finite quadrature separately, without interpolating or fitting it.
At `N=262144`, with `48/160/256` radial/beta/owner nodes, both fronts are
about `0.0398814289353` and their difference is enclosed by `6.55e-43`.
The known zero head is therefore not a significant quadrature contaminant
at this resolution. This pays only that particular numerical artifact.

## Remaining test and reproduction

The larger complete-response run retains both factorial faces and all
count/Riesz signs. Its full outer quadrature error is still unproved;
no partial row sum or fixed-point result replaces it. Even a resolved
continuum model would still need the literal-prime transfer and an
independent bound for the complementary carrier.

```sh
.lake/riesz-ball-venv/bin/python scripts/check_riesz_owner_integral.py
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_owner_phase.py \
  --output .lake/riesz-owner-phase-262144.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_owner_integral.py \
  --order 262144 --degree 224 --bits 6144 --taylor-order 224 \
  --compression 1e-80 --output .lake/riesz-owner-integral-262144-refined.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_owner_integral.py \
  --order 262144 --face 0 --degree 224 --bits 8192 --taylor-order 192 \
  --compression 1e-80 --output .lake/riesz-owner-integral-262144-lower.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_owner_head.py \
  --output .lake/riesz-owner-head-262144.json
.lake/riesz-ball-venv/bin/python scripts/probe_riesz_owner_coupled.py \
  --order 262144 --tnodes 48 --rnodes 160 --pnodes 256 \
  --subdivision 4 --degree 192 --bits 768 --projection-bits 384 \
  --workers 6 --output .lake/riesz-owner-coupled-262144-48-160-256.json
```
