# Full parameter averaging with the original source and complement retained

The complete circle of complex affine parameters can now be evaluated
exactly in Lean. Its bounded projection preserves the local xi-zero
source. Both projected strip segments have an independent quartic bound.
The full original correction still contains every genuine pole residue
and both signed large-value strip integrals. Their joint source ceiling
remains open.

This is a general resolvent identity applied to the actual xi/eta
carrier. It does not by itself supply a new zeta-specific cancellation
estimate or exclude a zero.

## Full arithmetic parameter family

Keep the actual spectral definitions

```
A(z)=xi(1/2+i*z),   E(z)=A(z)+i*A'(z),
C(z)=i*(1+Esharp(z)/E(z))/2.
```

At `E(z)!=0`, the original carrier equals `i*A(z)/E(z)`. Introduce

```
E_a(z)=a*A(z)+i*A'(z),   C_a(z)=i*A(z)/E_a(z).
```

The unit member is exactly the original denominator. On the original
regular domain, Lean proves

```
E_a=E*(1-i*(a-1)*C),
C_a=C/(1-i*(a-1)*C),
C_a-C_b=i*(a-b)*C_a*C_b   when E_a and E_b are nonzero.
```

The same family has the full cleared eta realization

```
J_a(s)=F(s)*eta'(s)+((a+R(s))*F(s)-F'(s))*eta(s),
G(s)*J_a(s)=F(s)^2*(a*xi(s)+xi'(s)),
partial_a J_a(s)=F(s)*eta(s).
```

Here `F=1-2*2^(-s)`, `G=s*(1-s)*Gamma_R(s)` and `R=G'/G`.
The completion identity includes dyadic exceptions for `Re(s)>0`,
`s!=1`; both extra dyadic factors stay explicit. On the full completion
domain at `s=1/2-i*z`, with `E(z)!=0`,

```
C(z)=i*logDeriv(a -> J_a(s))(1).
```

This derivative is in the coefficient parameter. It is not the spatial
logarithmic derivative of the previously constructed canonical unit.
For `Im(z)>=1/2`, the full complex family also has the proved floor
`Re(a)*abs(A(z))<=abs(E_a(z))`, hence no denominator zero if `Re(a)>0`.

See [SuzukiCarrierParameter.lean](../RiemannGaussian/SuzukiCarrierParameter.lean).

## Exact whole-circle evaluation

For `r>0`, let `M_r(z)` be the uniform mean of `C_(1+r*u)(z)` over
`abs(u)=1`. Set

```
P_r(z)=if r*abs(C(z))<1 then C(z) else 0.
```

At `E(z)!=0`, provided `r*abs(C(z))!=1`, the parameter trace is genuinely
circle integrable and Lean proves

```
M_r(z)=P_r(z),     abs(M_r(z))<1/r.
```

The excluded threshold is exactly the existence of a denominator zero
on the parameter circle. No value of a singular integral is used to
claim a mathematical average there. The cutoff `P_r` assigns zero at
the threshold explicitly and is measurable everywhere.

The general proof evaluates `average(c/(1-u*b))`. For `abs(b)<1`,
analyticity on the closed disk gives the value `c`. For `abs(b)>1`,
inverting the circle changes the integrand to `c*u/(u-b)`, analytic on
the disk with central value zero. This evaluates all phases together;
there is no search for finitely many coefficients.

See [ComplexResolventCircleAverage.lean](../RiemannGaussian/ComplexResolventCircleAverage.lean)
and [SuzukiCarrierCircleAverage.lean](../RiemannGaussian/SuzukiCarrierCircleAverage.lean).

## The original source survives

At every genuine xi zero `alpha=zetaSpectralCoordinate(rho)` of analytic
multiplicity `m`, there is a punctured neighborhood on which `M_r=P_r=C`.
The original denominator and the parameter-circle trace are regular
there. In particular, for an analytic remainder `p`,

```
M_r(z)/(z-alpha)^2 = (1/m)/(z-alpha)+p(z).
```

This applies to arbitrary multiplicities and to both reflected zero
nodes. It does not identify totalized values at common zeros with an
analytic extension. The terminal theorem is
`exists_suzukiXiParameterCircleAverage_source_model`.

The projection may change across its magnitude threshold. No global
holomorphy or contour deformation through that interface is asserted.

## Both strips and the complete correction

Use the original reflection weight `W=-(1/(z-alpha)-1/(z-conj(alpha)))^2`.
For `R>0`, `abs(l),abs(v)>=R`, and `2*abs(Re(alpha))<=R`, define the
projected strip correction with its original orientations:

```
S_small = i*integral_[0,1/2] W(v+i*y)*P_r(v+i*y) dy
        - i*integral_[0,1/2] W(l+i*y)*P_r(l+i*y) dy.
```

Both integrals are proved integrable, including all cutoff crossings
and both endpoints. Lean proves the independent estimate

```
abs(S_small)<=64*Im(alpha)^2/(r*R^4).
```

The complex complement `S_large` uses the same weights, orientations
and intervals with the density

```
if 1<=r*abs(C(z)) then W(z)*C(z) else 0.
```

On the actual admissible sides these are genuine integrals, and the
original mixed reflection strip correction is exactly `S_small+S_large`.
The original real Gram projection is its imaginary part.

Let `K` be the original mixed sum over **every** genuine carrier pole
in the rectangle, with all analytic pole orders retained. The final
compiled theorem `suzukiXiReflectionStripCorrection_large_error_le`
connects this decomposition directly to the original full target:

```
abs(originalCorrection - (2*pi*Re(Q_rho(K))-Im(S_large)))
  <=64*Im(alpha)^2/(r*R^4).
```

See [SuzukiCarrierProjectedStrip.lean](../RiemannGaussian/SuzukiCarrierProjectedStrip.lean).
For a fixed positive `r`, the error bound decays quartically with `R`.
The theorem is about removing the bounded part with a quantified error;
it is not an upper bound for the retained expression.

The remaining problem is to bound the complete signed combination of
all pole residues and both large-value integrals. Discarding the latter,
assuming the cutoff holomorphic, or estimating the number of poles as
though it bounded their residues would leave a gap. The previous exact
pole orders, local count bounds and canonical analytic-factor estimates
remain available for this problem.

This slice has local Lean validation only. Commits remain on hold.
