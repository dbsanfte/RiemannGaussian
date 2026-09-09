# Exact eta curvature in the full smooth reflection source

The full signed source of the actual smooth carrier now has a literal
eta expression, including at genuine carrier poles and common xi zeros.
The original finite eta prefixes recover both signed terms pointwise at
every genuine upper carrier pole. This supplies arithmetic access to the
[proved positive reflection-area source](suzuki-carrier-smooth-heat.md).
Its independent contradictory upper bound remains open.

## Common completion factor cancels exactly

In spectral coordinates keep `A(z)=xi(1/2+i*z)` and `E=A+i*A'`.
Set `s=1/2-i*z`. On the full completion domain

```
Re(s)>0,   s!=1,   1-2*2^(-s)!=0,
```

let `H` be the actual paired-eta completion factor and `Q=H'/H`, the
repository's explicit `pairedEtaArithmeticXiRegularCorrection`. Then

```
A(z)=H(s)*eta(s),
E(z)=H(s)*D(s),
D(s)=eta'(s)+(1+Q(s))*eta(s).
```

The completion factor is analytic and nonzero on this domain. Its
entire complex factor cancels in the homogeneous smooth quotient:

```
S_r(z)=i*eta(s)*conj(D(s))/(abs(D(s))^2+r^2*abs(eta(s))^2).
```

This identity does not require `eta(s)!=0` or `D(s)!=0`. Common-zero
values are transported from the globally smooth actual carrier, whose
local multiplicity models were proved in the preceding slice. For `r>0`,
the arithmetic quotient has norm at most `1/(2r)` everywhere.

The domain excludes the explicit completion singularities; it is not
silently extended through those exceptions. Every genuine upper carrier
pole lies in `0<Im(z)<1/2`, so its arithmetic coordinate lies in the
open strip `1/2<Re(s)<1`, inside this completion domain.

## The full signed source and its curvature cancellation

Keep the oriented spectral source `CG(f)=i*f_x-f_y`. Lean proves

```
CG(S_r)(z) = 2*i*r^2*eta(s)^2
              *conj(eta'(s)*D(s)-eta(s)*D'(s))
              /(abs(D(s))^2+r^2*abs(eta(s))^2)^2.
```

The leading `i` is required by the coordinate map `s=1/2-i*z`.
This is the source in spectral coordinates, not the Cauchy–Green source
in the eta coordinate. The exact identity holds also at `D=0` and at
common zeros, where its displayed numerator vanishes.

Differentiating the actual `D` then gives exactly

```
eta'*D-eta*D' = eta'^2-eta*eta''-Q'*eta^2.
```

The two terms `(1+Q)*eta*eta'` cancel. The completion curvature `Q'`
remains, with its full complex phase; `Q` also remains in `D` in the
positive smoothing denominator. No separate absolute bound discards
these couplings.

The terminal identities in
[SuzukiEtaSmoothSource.lean](../RiemannGaussian/SuzukiEtaSmoothSource.lean)
are `suzukiXiSmoothCarrierSource_eq_eta`,
`suzukiEtaCarrier_wronskian_eq_curvature`, and
`suzukiEtaSpectralSmoothSource_eq_curvature`.

For the original reflection weight `W` and spectral Gaussian `B`, the
complete actual area density is still

```
W(z)*(B(z)*V_r(s)-i*S_r(s)*H_heat(i*z)),
```

where `V_r` is the displayed spectral eta source and `H_heat` the existing
arithmetic-coordinate Gaussian source. Here `H_heat` is unrelated to the
completion factor `H`. Both signed area terms are retained in
`suzukiXiSmoothReflectionSource_eq_eta`; no carrier-pole exclusion is
introduced by that transport.

## Literal finite arithmetic recovery

Use exactly the repository's original finite paired eta prefix `eta_N`
and full completion correction:

```
D_N=eta_N'+(1+Q)*eta_N,
S_(r,N)=i*eta_N*conj(D_N)/(abs(D_N)^2+r^2*abs(eta_N)^2),
V_(r,N)=2*i*r^2*eta_N^2*conj(eta_N'*D_N-eta_N*D_N')
          /(abs(D_N)^2+r^2*abs(eta_N)^2)^2.
```

There is no coefficient search or selected numerical family. Every finite
prefix has the same exact cancellation:

```
eta_N'*D_N-eta_N*D_N'
 =eta_N'^2-eta_N*eta_N''-Q'*eta_N^2.
```

Locally uniform convergence of the actual eta prefixes and denominators,
with their proved analyticity, gives convergence of the derivatives.
Their full polynomial Wronskians converge to the actual curvature at
every point of the completion domain, including common zeros.

For fixed `r>0`, if `eta(s)!=0` or `D(s)!=0`, the limiting smoothing
denominator is genuinely positive. Lean therefore proves pointwise
convergence of both `S_(r,N)` and `V_(r,N)`, and of the complete same-prefix
reflection density with both Gaussian terms.

In particular, every actual upper carrier pole satisfies the required
arithmetic domain and noncommon-zero condition. The terminal theorem
`tendsto_suzukiEtaFiniteSmoothReflectionSource_at_upper_pole` derives
these conditions from `Im(z)>0`, `E(z)=0`, and `A(z)!=0`, and covers
all analytic pole orders. See
[SuzukiEtaFiniteSmoothSource.lean](../RiemannGaussian/SuzukiEtaFiniteSmoothSource.lean).

## Remaining independent inequality

The original weighted area has the proved iterated source
`2*pi*i*B(beta)/m`, with positive imaginary part under a hypothetical
right-half zero. The new arithmetic identity and recovery do not bound
that quantity from the opposite side.

The next task is to estimate the full signed eta curvature and Gaussian
companion together, strongly enough to obtain an independent upper bound
strictly below the positive source. Pointwise finite recovery alone does
not permit exchange with the area, shrinking-puncture or expanding-window
limits. In particular, quotient convergence at common numerator/denominator
zeros is not asserted. No new zero exclusion or RH proof follows here.
