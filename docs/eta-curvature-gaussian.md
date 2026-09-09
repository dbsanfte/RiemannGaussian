# Eta curvature: exact pairs and a uniform Gaussian bound

The actual infinite eta function now has an unconditional bound for its
bare curvature. For every real `sigma > 0`, every real center `x`, and
`0 < tau <= log(2)/32`, Lean proves

```text
norm integral_R exp(-tau*(t-x)^2) *
  [eta'(sigma+i*t)^2 - eta(sigma+i*t)*eta''(sigma+i*t)] dt
 <= 2*sqrt(pi/tau)*exp(-(log 2)^2/(8*tau)).
```

The norm is outside the complex integral. This does not bound the integral
of the absolute value. The estimate is uniform in both the vertical line
and its center. Lean also proves convergence to zero as `tau -> 0+` for
arbitrary moving centers and arbitrary moving positive real parts, without
a lower bound on those real parts or a growth restriction on the centers.

The terminal results are
[`norm_integral_pairedEta_curvature_gaussian_le`](../RiemannGaussian/EtaCurvatureGaussianLimit.lean)
and `tendsto_pairedEta_curvature_gaussian_moving` in that module. All results
in this slice pass the local verification gates. No new zero
exclusion or independent bound for the complete reflection source follows.

## Exact signed arithmetic

For an arbitrary finite Laplace sum

```text
f(s) = sum_j c_j exp(-s*l_j),
```

Lean proves

```text
f'(s)^2 - f(s)*f''(s)
 = -1/2 * sum_(j,k) c_j*c_k * exp(-s*(l_j+l_k)) * (l_j-l_k)^2.
```

The coefficients are complex and bilinear. The squared difference of
frequencies controls the amplitude; their sum controls the oscillation.
There is no conjugation of one coefficient and no Hermitian positivity
claim. Each self-pair vanishes exactly. The general statement and
differentiation laws are in
[`FiniteLaplaceCurvature.lean`](../RiemannGaussian/FiniteLaplaceCurvature.lean).

[`EtaBilinearCurvature.lean`](../RiemannGaussian/EtaBilinearCurvature.lean)
applies this to the unchanged eta prefix ending at `2N`. Its pair kernel is

```text
L_N(s) = sum_(1<=m,n<=2N)
  sign(m)*sign(n) * (m*n)^(-s) * (log(m)-log(n))^2.
```

Both parity signs and the original integer-product phase remain explicit.
The complete finite sums tend to `-2*(eta'^2-eta*eta'')` throughout
`Re s > 0`, including eta zeros. This convergence does not rearrange the
conditionally convergent unpaired terms into separate infinite channels.

For the actual finite smoothed source, let

```text
D_N = eta_N' + (1+Q)*eta_N,
d_N = abs(D_N)^2 + r^2*abs(eta_N)^2.
```

The full source is exactly

```text
-i*r^2*eta_N^2 * conj(L_N + 2*Q'*eta_N^2) / d_N^2.
```

This identity includes the completion curvature, the full denominator, and
the totalized finite values. Its domain is the existing completion domain.
It supplies no sign estimate by itself.

## Gaussian estimate and the infinite limit

[`EtaCurvatureGaussian.lean`](../RiemannGaussian/EtaCurvatureGaussian.lean)
first evaluates the complete finite Gaussian transform with all pair
phases intact. Its damping factor is
`exp(-(log(m)+log(n))^2/(4*tau))`.

For positive integer frequencies, every surviving pair has
`log(m)+log(n) >= log(2)`. The sole zero-frequency pair has zero gap.
A real Gaussian inequality bounds the full gap amplitude by

```text
(m*n)^(-2) * exp(-(log 2)^2/(8*tau)).
```

The inverse-square sums each have bound two. Consequently the finite
estimate is uniform in the cutoff and in **every** complex coefficient
family with `abs(c_n) <= 1`, at every nonnegative real tilt. Eta's actual
alternating coefficients satisfy this condition.

[`EtaCurvatureGaussianLimit.lean`](../RiemannGaussian/EtaCurvatureGaussianLimit.lean)
then proves a cutoff-independent positive-half-plane bound for eta prefixes
and Cauchy bounds for every fixed derivative order. The first two orders
give one polynomial majorant for the curvature on each positive vertical
line. Its product with the Gaussian is integrable. Dominated convergence
therefore proves genuine integrability of the infinite curvature and
justifies the prefix limit under this Gaussian integral. Finally, the
explicit envelope tends to zero and controls arbitrary moving lines and
centers.

## Remaining source inequality

The target is still an independent signed bound below the positive source
of the complete reflection area. Its density retains both

```text
W * B * 2*i*r^2*eta^2*conj(eta'^2-eta*eta''-Q'*eta^2) / d^2
```

and the companion `-i*W*S_eta*H_heat`.

The new estimate concerns the Gaussian average of `eta'^2-eta*eta''`
alone. Multiplication by the remaining functions changes the frequency
coupling. In particular, products with conjugated phases can have zero
total frequency even when the original self-pairs vanished. No estimate
for that coupled integral, no signed source ceiling, and no RH conclusion
is asserted. The justified prefix/Gaussian exchange above also does not
exchange the original area, excision, or expanding-window limits.
