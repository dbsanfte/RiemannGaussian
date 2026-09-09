# Signed cancellation of the complete Suzuki correction costs

`SuzukiSignedLegendreRemainder.lean` proves a one-sided, unnormalized
comparison between the original canonical gap and an explicit finite
arithmetic potential. It also proves that the leading quadrature and
transport costs cancel when summed with their original signs.

The independent lower bound on the arithmetic potential remains open.
This slice improves the proved comparison error; it does not prove RH or
give a new zero exclusion.

## The finite arithmetic expression

At the original endpoint `N=count+2`, write

```text
M_N = sum_{2<=n<=N} Lambda(n)/sqrt(n),
P_N = sum_{2<=n<=N} Lambda(n)*log(n)/sqrt(n),
c   = suzukiArchimedeanSlopeConstant = -Re(zeta'/zeta)(1/2),
m_N = M_N-c,
C   = suzukiHurwitzLerchTwo(1)/4-8.

B_N = P_N - 2*m_N*(log(m_N/2)-1) + C.
```

`suzukiMassLegendrePotential count` is this expression, with the complete
original prime-power mass and logarithmic moment. The argument `m_N/2`
is proved positive from the existing exact slope-matching law. No
implicit canonical center occurs in the definition of `B_N`.

If `G_N` denotes the unchanged canonical gap, Lean proves

```text
0 <= B_N-G_N <= (16/75)*exp(5)/N^(5/2).
```

Moreover, `B_N-G_N` is decreasing along the actual arithmetic schedule
and tends to zero without normalization. The compiled declarations are
`suzukiMassLegendrePotential_sub_gap_bounds`,
`suzukiMassLegendrePotential_sub_gap_le_inv_five_halves`,
`antitone_suzukiMassLegendrePotential_sub_gap`, and
`suzukiMassLegendrePotential_sub_gap_tendsto_zero`.

## The signed cancellation

Let `a_j` be the original new atom and let

```text
Phi(m) = 2*m*(log(m/2)-1),
Q_j = Phi(m_{j+1})-Phi(m_j)-2*a_j*log(m_j/2).
```

`suzukiMassLogQuadratureCost_bounds` proves
`0<=Q_j<=2*a_j^2/m_j`. Summing the full logarithm gives exactly

```text
L_j = B_{j+1}-B_j+Q_j,
I_j = L_j+E_j,
G_{j+1}-G_j = I_j-C_j,
```

where `E_j` is the existing positive Lerch work error and `C_j` the
existing positive canonical transport cost. Hence, with `delta_j=B_j-G_j`,

```text
sum_{j=s}^{s+k-1} (Q_j+E_j-C_j) = delta_s-delta_{s+k},
0 <= sum_{j=s}^{s+k-1} (Q_j+E_j-C_j)
     <= (16/75)*exp(5)/(s+2)^(5/2).
```

The last bound is independent of band length. It is checked by
`sum_suzuki_signed_cost_eq_gap_sub_massLegendre` and
`sum_suzuki_signed_cost_bounds`; uniform decay follows in
`sum_suzuki_signed_cost_uniformly_small`. Thus a lower bound on a change
of `B` transfers to the same change of the actual gap with a nonnegative
correction. These are estimates of the net signed cost, not separate
absolute estimates of its components.

## Why the error is this small

The zeroth Lerch value mode cancels the decaying exponential exactly:

```text
A(r) = 4*exp(r/2)+c*r+C-V(r),
(4/25)*exp(-5*r/2) <= V(r) <= (16/75)*exp(-5*r/2).
```

At the original canonical center, the corrected mass is
`m=2*exp(r/2)+T(r)`. Legendre cancellation gives

```text
B-G = V(r)-R(r),
R(r) = 2*m*log(1+T(r)/(2*exp(r/2)))-2*T(r),
0 <= R(r) <= T(r)^2/exp(r/2).
```

The existing positive slope-tail estimate controls `R`; the retained
first value-tail mode proves `R<=V`. Finally, the previously proved
`r>=log(N)-2` yields the displayed integer-cutoff bound.

The sign of the band correction is also proved directly. Differentiating
the smooth comparison error with respect to its original center gives

```text
(r-2*log((A'(r)-c)/2))*A''(r) <= 0.
```

All differentiation domains, positive logarithm arguments, and curvature
conditions are discharged. Monotonicity of the original centers then
transfers this sign to the actual arithmetic sequence.

## Remaining target

The correlated expression `P_N-Phi(M_N-c)+C` still needs an independent
lower bound sufficient for the existing RH implication. The positive
comparison error does not prove such a bound. Separately estimating the
mass and logarithmic moment would again discard their shared arithmetic
information.

The proof uses the repository's existing Legendre and Lerch decompositions.
No novelty claim is made. Validation is local and commits remain held.
