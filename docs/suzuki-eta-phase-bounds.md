# Signed dyadic control on actual Suzuki contours

The subsequent [signed square estimate](suzuki-eta-signed-square.md)
uses the full complex identities here to prove a quartic floor for the
integrated completed remainder on oriented phase contours. Its negative
part tends to zero; the complete joint source ceiling remains open.

The dyadic completion is now bounded independently on genuine expanding
contours. This controls one part of the arithmetic carrier; it does not
establish the independent joint source ceiling or exclude any new zeros.

## Exact phase and amplitude

Write `ell=log(2)`, `w(s)=2*2^(-s)`, and `F(s)=1-w(s)`. Lean proves

```
Re(w) = 2*exp(-Re(s)*ell)*cos(Im(s)*ell),
|w|^2 = 4*exp(-2*Re(s)*ell),
F'/F = ell*w/(1-w).
```

For `cos(Im(s)*ell)<=0`, the real part of `w` is nonpositive and

```
|F|^2 >= 1+|w|^2,
|F'/F + ell/2| <= ell/2.
```

Thus the factor stays nonzero even across `Re(s)=1`. On the closed strip
`1/2<=Re(s)<=1`, the exact amplitude also gives `1<=|w|^2<=2`, hence

```
ell/2 <= -Re(F'/F) <= 2*ell/3.
```

The full complex disk is retained alongside this sharper real enclosure.
The compiled theorems are
`norm_pairedEtaFactorLogDerivative_add_half_le` and
`pairedEtaFactorLogDerivative_re_phase_strip_bounds` in
[EtaDyadicPhaseBounds.lean](../RiemannGaussian/EtaDyadicPhaseBounds.lean).

## Genuine contours with these phases

At spectral coordinate `z=v+i*y`, the arithmetic argument is
`s=1/2+y-i*v`. Its dyadic cosine is `cos(v*ell)`, independent of `y`.
Open negative-cosine bands contain points avoiding the full xi/carrier
singular set and all dyadic exceptions. Arbitrarily large scales `R`
have favorable bands in both required unit windows
`(-R-1,-R)` and `(R,R+1)`.

`exists_suzukiXiEtaPhase_contour_family` constructs the actual contours
beyond any prescribed inner size, with `R(n)->infinity`. The top side
retains the existing admissibility conditions. Both closed vertical strip
segments satisfy the signed completion bounds at every height. See
[SuzukiEtaPhaseContours.lean](../RiemannGaussian/SuzukiEtaPhaseContours.lean).

## The actual finite arithmetic expression

Let `e=eta_N(s)`, `e'=eta_N'(s)`, and let the existing correction be

```
R(s) = 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2.
D_N = e' + (1+R-F'/F)*e,
C_N = i*e/D_N.
```

The same original eta coefficients and true denominator remain in use.
Lean proves the exact identity

```
Re(e*conj(D_N)) = Re(e*conj(e')) + (1+Re(R)-Re(F'/F))*|e|^2.
```

The dyadic contribution to `Im(C_N)` therefore lies between
`(ell/2)*|C_N|^2` and `(2*ell/3)*|C_N|^2`. This statement subtracts the
remaining signed term

```
[Re(e*conj(e'))+(1+Re(R))*|e|^2] / |D_N|^2.
```

It does not assign a sign to that term. The theorem is
`suzukiEtaFiniteCarrier_im_phase_strip_energy_bounds`.

For arbitrary `B:Complex`, define the centered numerator using
`D_center=e'+(1+R+ell/2)*e`. The richer identity is

```
B*e*conj(D_N) - B*e*conj(D_center)
  = -B*conj(F'/F+ell/2)*|e|^2.
```

Consequently

```
|Im(B*C_N) - Re(B*e*conj(D_center))/|D_N|^2|
  <= |B|*|C_N|^2*ell/2.
```

The centering changes only the displayed numerator. Its denominator is
still the actual `D_N`, not `D_center`. No lower bound for `D_N` or
smallness of the carrier energy is asserted. The algebraic finite
identities respect Lean's totalized division; actual contour use relies
on the already proved eventual finite-denominator nonvanishing. See
`suzukiEtaFiniteCarrier_im_phase_energy_error` in
[SuzukiEtaPhaseEnergy.lean](../RiemannGaussian/SuzukiEtaPhaseEnergy.lean).

## The complete limit is preserved

Finite recovery is now also proved for any supplied admissible expanding
contour family. Applying it to the phase-constrained family preserves
every genuine pole, both strip sides, the lifted contour's exact xi
source, and error below `1/(n+1)` with growing common eta truncations.
The selected truncation at every stage now explicitly has nonzero finite
denominators on all observation paths, including both full strip
segments. Genuine weighted path integrability follows for each selected
regular truncation. See
[SuzukiEtaObservationRegularity.lean](../RiemannGaussian/SuzukiEtaObservationRegularity.lean).

For a hypothetical right-half zero the finite joint correction still
converges to

```
2*pi/m_rho + reflectionBoundaryEnergy(rho).
```

The energy is strictly positive. The compiled terminal theorem is
`exists_suzukiXiEtaFiniteReflection_phase_recovery` in
[SuzukiEtaPhaseRecovery.lean](../RiemannGaussian/SuzukiEtaPhaseRecovery.lean).

An independent eventual ceiling at `2*pi/m_rho+o(1)` would contradict
this limit. The present completion estimate does not provide that
ceiling: the remaining eta/derivative interaction, its true denominator,
and the complete signed pole correction still require arithmetic control.
The disk radius is a fixed coefficient multiplying the carrier energy;
it is not a vanishing error by itself.
