# Exact cancellations inside the original arithmetic carrier

Lean now removes supported portions of three original complex amplitudes
whose sum is **exactly zero**. These portions incur no chord-error charge.
The whole original carrier is bounded by its initial absolute mass minus
the accumulated exact saving, with every remaining amplitude retained.

Every successful cycle saves at least twice its smallest available
amplitude. Two nearby flanks around an opposite direction need only
quadratic extra partner mass. These are quantitative local estimates;
sufficient aggregate arithmetic capacity at source scale remains open.
**No new zero-free region or RH proof follows from this slice.**

## Exact zero cycles and their capacity

For complex amplitudes z, w and v, let

```math
[z,w]=\operatorname{Im}(\overline z w).
```

The planar determinant identity gives

```math
[w,v]z+[v,z]w+[z,w]v=0.
```

When all three signed areas are positive, their directions surround the
origin. `cycleScale` divides by the largest area, so each removed fraction
lies in [0,1] and at least one original amplitude is exhausted. Otherwise
the step removes zero. This is a fully specified construction, with no
assumed cancellation or independent choice of filter coefficients.

`sent_cycle_eq_zero` proves exact cancellation of the removed portions.
`sum_cycle_remainders` preserves the whole complex sum. Every remainder
is a nonnegative multiple of its previous amplitude. `cycleSaving` is
exactly the sum of the removed norms, and
`twice_min_norm_le_cycleSaving` proves

```math
\operatorname{saving}(z,w,v)\ge
2\min(|z|,|w|,|v|)
```

on every successful branch. The proof uses both exhaustion and the
triangle inequality for a sum known to be exactly zero; it does not
assume comparable original amplitudes.

## The arithmetic phase test keeps the full filter

For P=1 an actual atom is a signed real Riesz coefficient times its
nonnegative factorial envelope and exp(-it log n). Its exact oriented
cross-term is

```math
[B_i,B_j]=a_i a_j\sin\!\left(t\log(i/j)\right).
```

For the full complex polynomial filter, put
C = conjugate(B_i(0)) B_j(0). `area_actual_full` retains both channels:

```math
[B_i(t),B_j(t)]
=\Re C\,\sin\Delta+\Im C\,\cos\Delta,
\qquad\Delta=t\log(i/j).
```

Thus the construction keeps the Riesz signs, all polynomial directions,
and the logarithmic product correlations. There is no restriction to
semiprimes or a single coefficient family. The companion midpoint
identity also preserves both signed trigonometric channels and the
common phase of each transported pair before taking any norms.

## Nearby opposite flanks have quadratic overhead

Let the directions be theta, theta+pi-a, theta+pi+b, with a,b positive
and a+b less than pi. The exact partner weights are forced by

```math
\sin(a+b)e^{i\theta}
+\sin b\,e^{i(\theta+\pi-a)}
+\sin a\,e^{i(\theta+\pi+b)}=0.
```

Cancelling central mass A requires A sin(b)/sin(a+b) from the first
partner and A sin(a)/sin(a+b) from the second. Their combined mass divided
by A is `bracketOverhead`. For both gaps at most delta <= 1,

```math
1\le H(a,b)=\frac{\sin a+\sin b}{\sin(a+b)}
\le\frac1{1-\delta^2/2}\le1+\delta^2.
```

`bracketOverhead_sub_one_le_sq` proves the quadratic excess. The actual
available central mass is determined by all three amplitudes:

```math
m=\min\!\left(A,\frac{B\sin(a+b)}{\sin b},
                    \frac{C\sin(a+b)}{\sin a}\right).
```

`norm_bracket_le_capacity` proves the complete bound

```math
\left|Ae^{i\theta}+Be^{i(\theta+\pi-a)}
       +Ce^{i(\theta+\pi+b)}\right|
\le A+B+C-m(1+H(a,b)).
```

All shortages and excess partner masses are included. The existence of
nearby primes alone does not establish sufficient weighted capacity.
Signs, amplitude supply, competition between cycles and their dependence
on the moment order remain part of the arithmetic problem.

## Whole-carrier bound and unchanged source

`cycleResidual` applies successive tests to the available remainders.
Shared labels may occur again, but spent mass cannot be reused. The
canonical `actualCycles` includes all ordered distinct triples of the
original band, testing the positive branch inside each step.
`norm_actual_band_le_exact_cycles` bounds the entire original carrier,
with its original support, actual cutoff and full polynomial.

Later pair transport can act on this exact-cycle remainder.
`norm_actual_band_le_cycles_then_transport` charges **all** resulting
sent chords and final unmatched mass. It does not assert that one greedy
ordering dominates every other ordering, or that fallback is free.

The terminal
[`tendsto_actual_cycle_source`](../RiemannGaussian/ZetaRieszCycleSource.lean)
retains

```math
u^{N+1}\sum_n B^{\mathrm{remaining}}_N(n)\longrightarrow-m(\rho),
\qquad u=\frac32-\Re\rho,
```

at every hypothetical right-half zero, using the full pole-jet polynomial
and unrestricted multiplicity. No exposure or simplicity is required.
This source identity does not bound the remainder independently.

The next mathematical obligation is sufficient aggregate arithmetic
capacity, or another independent bound on this complete remaining sum.
A fixed finite percentage saving is not enough to overcome a growing
absolute allowance. Small floating-point physical-annulus probes are
exploration only, on their explicitly restricted support. They do not
supply a full original-band certificate or run in ordinary CI.

These seven arithmetic modules are imported by the ordinary root.
Default RH, zero-free and numerical-certificate endpoints and both
top-ten lists remain unchanged. No historical novelty claim is made for
the determinant or trigonometric identities.

[Arithmetic supply bounds](zeta-riesz-arithmetic-cycles.md) now retain the
exact cofactor target and separate capacities in a proved whole-carrier
budget, with all complex filters and nonunit squarefree cofactors covered.
Sufficient aggregate source-scale control remains open.
