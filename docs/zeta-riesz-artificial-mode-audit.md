# Finite artificial-mode renormalization: the two gates

**Arbitrary fixed complex negative modes retain triangular support. The
one-variable interpolation and geometric decay theorem are valid. The
proposed extension to joint pole removal fails for the same toy remainder.**

This continues the [local analytic-factor audit](zeta-riesz-local-analytic-audit.md).
It preserves the genuine local xi decomposition, all low-order channels,
every prior packet/rest ledger and the infinite-mode Gamma-growth audit.
It does not change an arithmetic carrier or return to physical cutoffs.

The requested further iteration produced a
[causal pole-surface subtraction and radial regression bound](zeta-riesz-causal-surface.md).
That continuation preserves the fixed-mode obstruction here and instead
controls the toy response quantitatively on the growing strict core.

The new proofs are in
[ZetaRieszArtificialModeAudit](../RiemannGaussian/ZetaRieszArtificialModeAudit.lean).

## The one-variable theorem passes

For h!=0, choose a logarithm b with exp(b)=h and set

$$
a_m=1-\exp(-b/m),\qquad R_m(t)=(1-a_m t)^{-m}.
$$

`sliceFactor_offset_one` and `offset_tendsto_zero` prove the exact value
R_m(1)=h and a_m->0 using a coherent logarithmic root choice.
`exists_small_interpolator` proves that the parameter can be arbitrarily
small. `slice_denominator_ne_zero` and `analyticOnNhd_sliceFactor` keep its
poles outside any prescribed fixed disk. A zero parameter corresponds to
the trivial factor and needs no artificial mode.

`normalized_endpoints` gives H/R_m=1 at both 0 and 1 when H(0)=1 and
R_m(1)=H(1)!=0. `exact_factorization` proves the decomposition of the same
response without modifying its value.

`slice_removable` proves the selected simple pole removable whenever
Q(1)=H(1). `slice_analytic_extension` patches the quotient across 1 on the
whole working disk. `slice_geometric` gives, for any intermediate radius
1<q<r, a bound M/q^n for its Taylor coefficient norms, provided P0, H and
Q are analytic on |t|<r. Thus the proposed one-variable argument is proved,
not rejected on the strength of the earlier counterexample.

## The support theorem already allows artificial locations

The existing `ZetaRieszNegativeModeSupport.inversePrimitive_support` is
generic in an arbitrary finite index set and arbitrary complex locations.
It does not require the locations to be actual zeta zeros.

`augmented_support` applies it to the selected mode plus any fixed finite
artificial family. `augmented_response` identifies the corresponding exact
count transform. Repeated entries retain their negative multiplicities.
The empty-cofactor term and all diagonal derivative channels remain.

For a nonzero a, the exact two-variable lift of (1-at)^(-m) is

$$
\xi=1-\frac1a,\qquad
Q_m(w,z)=\left(\frac{w-\xi}{w+z-\xi}\right)^m.
$$

`repeated_factor_path` proves Q_m(1,-t)=(1-at)^(-m). The location xi must
be fixed with respect to w,z to apply this support theorem.

## What fails in the joint lift

Use the previous exact toy factor

$$
H(w,z)=\frac{w+z+1}{w+1},\qquad P(w,z)=\frac{w}{w+z}.
$$

The selected divisor is the surface w+z=0, not just its point (1,-1).
For any finite fixed family A, let

$$
Q_A(w,z)=\prod_{i\in A}\frac{w-\xi_i}{w+z-\xi_i}.
$$

The exact residual in `response_split` is

$$
E_A(w,z)=\frac{w}{w+z}\frac{Q_A(w,z)-H(w,z)}{z^2},
$$

and the other summand is precisely the supported finite negative-mode
response. This is an identity of the full two-variable transform.

For artificial modes away from the selected location xi=0,
`residual_normal_residue` proves

$$
\lim_{z\to-w}(w+z)E_A(w,z)
=\frac1w\left[
\prod_{i\in A}\left(1-\frac{w}{\xi_i}\right)-\frac1{w+1}
\right].
$$

Hence cancellation along the divisor requires matching a function of w.
The artificial trace is a polynomial. The analytic factor's trace is
1/(w+1). They cannot agree on any open neighborhood of w=1.
`not_eventually_surface_match` proves this for **every finite fixed
complex family**, allowing distinct modes and repeated modes alike.
The proof uses the analytic identity theorem: if (w+1) times that polynomial
were identically 1 near 1, it would be identically 1 everywhere, contradicting
its value 0 at w=-1.

`not_continuousAt_residual` identifies each nonzero residue as a genuine
nonremovable pole. `frequently_residual_pole` proves that every neighborhood
of w=1 contains such a pole. Thus matching H(1) removes the pole on the
chosen slice but cannot produce the claimed joint removable singularity or
a uniform coefficient radius beyond the selected pole on nearby normalized
slices z=-w*t.

This is a failure of the proposed joint pole-removal argument. It is not a
proof that every coupled estimate fails, that a literal packet diverges,
or that the actual zeta remainder equals this toy model. In particular,
nondecaying coefficients alone are not a below-diagonal inverse estimate;
the earlier audit separately proved the toy ordinary inverse.

Allowing xi to depend on w could match values separately, but would cease
to be a fixed finite-mode factor. The existing diagonal-convolution support
theorem does not apply to that new operator. No claim about such an operator
is made here.

## Numerical regression

The optional probe reproduces the proposed m=8 table exactly to the displayed
precision:

| N | Absolute residual coefficient at w=1 |
|---:|---:|
| 1 | 0.2240618613 |
| 3 | 0.01813138976 |
| 5 | 0.0007974532196 |
| 8 | 0.000004037799684 |
| 12 | 1.865949435e-9 |
| 16 | 5.641020340e-13 |

Here a=-0.090507732665..., the t-pole is -11.048779707..., and the fixed
two-variable mode location is xi=12.048779707.... On nearby normalized
slices, the coefficients instead converge to the surface mismatch:

| w | Limiting residual coefficient, m=8 |
|---:|---:|
| 0.99 | +0.001119235585 |
| 0.999 | +0.0001120205720 |
| 1 | 0 |
| 1.001 | -0.0001120412059 |
| 1.01 | -0.001121299544 |

The probe tests m=8,16,64 and coefficients through N=4096. It evaluates
the remaining binomial tail directly through its convergent hypergeometric
formula, avoiding cancellation of two nearly equal floating-point values
on the interpolated slice. It is exploratory and separate from Lean and CI:

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_artificial_modes.py \
  --output docs/riesz-artificial-mode-probe.json
```

The first gate passes. The fixed-slice regression passes. The second,
joint-transform gate fails as formulated. Work stops before physical
cutoff, broad-packet or arithmetic-floor claims. The public mathematical
frontiers remain unchanged.

A subsequent [causal surface test](zeta-riesz-causal-surface.md) bypasses
this particular obstruction by matching the whole pole trace with a
cutoff operator. Its source-matched radial regression is proved small;
the corresponding estimate for the actual zeta remainder remains open.
