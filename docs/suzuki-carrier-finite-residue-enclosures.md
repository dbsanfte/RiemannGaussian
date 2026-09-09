# Signed tail control and finite carrier-residue enclosures

The complete signed xi tail now controls its own complex derivative.
At genuine upper carrier poles this gives finite slope disks, and their
inversion gives signed enclosures of the full weighted residue matrix.
The estimates retain every finite complex weight and reflected phase.
They do not establish the independent source ceiling required for RH.

## Coordinates and the fixed window

Write

```
A(z) = xi(1/2+i*z),   q(z) = A'(z)/A(z),
q_T(z) = sum_{rho in spectralZetaZeroWindow T} m_rho/(z-alpha_rho),
alpha_rho = -i*(rho-1/2),   E(z) = A(z)+i*A'(z).
```

All multiplicities are actual analytic multiplicities. The symmetric
zero window stays fixed when taking derivatives; the centered local band
whose selection varies with `Re(z)` is not differentiated.

`exists_riemannXiSignedWindowTail` constructs an analytic representative
of `q-q_T` on

```
abs(Re(z))+1/2 < T,   0 < Im(z) < 1.
```

Its imaginary part is nonpositive throughout that domain, including
through the removed xi zeros. Away from the finite divisor it equals
the literal raw remainder. The sign extends by continuity from the
complete paired expansion; totalized values at singularities are not
used as analytic values.

## Quantitative control of the entire omitted derivative

The generic half-plane estimate is

```
norm(f'(c)) <= 2*(-Im(f(c)))/R
```

when `f` is holomorphic on the radius-`R` disk about `c`, `R>0`, and
`Im(f)<=0` there. The proof includes the case `Im(f(c))=0` and needs no
strict positive allowance. See
`norm_deriv_le_of_im_nonpos_on_ball` in
[AnalyticHalfPlaneDerivative.lean](../RiemannGaussian/AnalyticHalfPlaneDerivative.lean).

For `A(c)!=0`, `0<Im(c)<1/2`, and `T>=abs(Re(c))+1`, the radius-`Im(c)/2`
disk lies in the signed-tail domain. Consequently

```
norm(q'(c)-q_T'(c)) <= 4*(Im(q_T(c))-Im(q(c)))/Im(c).
```

This is `norm_deriv_logDeriv_riemannXiSpectral_sub_window_le`.
The derivative of the finite head is proved to be the literal sum

```
q_T'(c) = sum_{rho in spectralZetaZeroWindow T} -m_rho/(c-alpha_rho)^2.
```

The complete xi expansion makes the displayed allowance tend to zero.
Lean deduces both the omitted derivative's decay and `q_T'(c)->q'(c)`.
All of these statements are in
[RiemannXiSignedTailDerivative.lean](../RiemannGaussian/RiemannXiSignedTailDerivative.lean).

## Genuine carrier poles and finite slope margins

At a genuine upper pole, `E(c)=0`, `A(c)!=0`, and `Im(c)>0`. The existing
safe-half-plane theorem gives `Im(c)<1/2`, and the exact pole equation
gives `q(c)=i`. Thus define

```
a_T = q_T'(c),
e_T = 4*(Im(q_T(c))-1)/Im(c) >= 0,
margin_T = norm(a_T)-e_T.
```

The entire actual slope satisfies

```
norm(q'(c)-a_T) <= e_T,
margin_T <= norm(q'(c)).
```

If `margin_T>0`, then `q'(c)!=0` and `E'(c)=i*A(c)*q'(c)!=0`, so the
actual pole is simple. Simplicity is a conclusion of this finite bound.
At every actual simple upper pole the margins converge to
`norm(q'(c))>0`, hence are eventually positive. No common positive lower
bound over different poles is asserted.

See `analyticOrderNatAt_suzukiXiEValue_eq_one_of_finite_margin` and
`eventually_suzukiXiFinitePoleSlopeMargin_pos_at_simple_pole` in
[SuzukiCarrierFiniteSlopeBound.lean](../RiemannGaussian/SuzukiCarrierFiniteSlopeBound.lean).

## Retaining the signed residue

For an arbitrary finite genuine-zero set `S` and arbitrary complex
weights `w`, retain

```
P_w(z) = sum_{rho in S} w_rho/(z-alpha_rho),
B_w(c) = conj(P_w(conj(c)))*P_w(c).
```

The exact full weighted simple-pole residue is `B_w(c)/q'(c)`. In
particular, `B_w(c)` is not replaced by a norm square at the nonreal pole.

For a positive margin, put

```
D_T = normSq(a_T)-e_T^2 > 0,
center_T(w,c) = B_w(c)*conj(a_T)/D_T,
radius_T(w,c) = norm(B_w(c))*e_T/D_T.
```

The disk-inversion identity and estimate in
[ComplexInverseDisk.lean](../RiemannGaussian/ComplexInverseDisk.lean)
give the actual carrier bound

```
norm(full_weighted_residue(w,c)-center_T(w,c)) <= radius_T(w,c).
```

The phase of `B_w(c)*conj(a_T)` stays in the center. The corresponding
real-part error bound retains its sign. At each actual simple upper pole,
`radius_T(w,c)->0` and `center_T(w,c)` converges to its exact weighted
residue, for every fixed finite family `w`.

The formulas use finite actual zero data and the actual pole coordinate.
They do not construct all those coordinates or bound their aggregate
arithmetic behavior.

## The full finite matrix, simultaneously for all weights

For a fixed finite set `C` of genuine upper poles with positive margins,
let `K_C(rho,sigma)` be the sum of their exact mixed residues. Lean proves

```
Re(sum_{rho,sigma in S} conj(w_rho)*w_sigma*K_C(rho,sigma))
  <= Re(sum_{c in C} center_T(w,c)) + sum_{c in C} radius_T(w,c).
```

This is `re_suzukiXiPole_matrix_le_finite_centers`. The complex centers
are combined before their real part is taken; their possible cancellation
is preserved. Only the approximation errors are bounded by their summed
radii. The stronger complex-disk statement remains available upstream.

If all poles in the fixed set `C` are simple, one sufficiently large
window works simultaneously for **all** finite node sets and complex
weight families. This quantifier order is proved by
`eventually_suzukiXiPole_matrix_enclosure_all_weights`. The total radius
tends to zero for each fixed family by
`tendsto_sum_suzukiXiFinitePoleResidueRadius_zero`.

These terminal results are in
[SuzukiCarrierFiniteResidueDisk.lean](../RiemannGaussian/SuzukiCarrierFiniteResidueDisk.lean).

## The remaining source ceiling

The live target remains an independent bound

```
J_R = 2*pi*Re(Q_rho(K_R))-Re(Q_rho(S_R)) <= 2*pi/m_rho+o(1).
```

The constructed joint limit at a hypothetical right-half zero is
`2*pi/m_rho+E_rho` with `E_rho>0`; the displayed upper bound would
therefore contradict that zero. It is not proved here.

The signed centers still need a bound together with the two oriented
strip sides. The full `K_R` retains arbitrary-order carrier poles, whereas
the disk inversion here handles simple poles. A fixed finite-set limit
also does not control expanding pole sets or a vanishing minimum slope.
Those issues require a bound for complete pole groups or additional
actual-zeta arithmetic. No new zero has been excluded, and no simplicity
assumption is inserted into the global RH chain.

The [finite eta contour construction](suzuki-eta-pole-groups.md) now
recovers complete pole groups of arbitrary order on fixed admissible
rectangles inside the open spectral strip. It uses the actual arithmetic
denominator and keeps the exact xi source. Its signed approximation bound
does not establish the global source ceiling or an expanding-contour bound.
