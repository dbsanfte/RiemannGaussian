# The signed carrier inside Suzuki's arithmetic Gram

[SuzukiCarrierPhase.lean](../RiemannGaussian/SuzukiCarrierPhase.lean)
proves a signed representation of the genuine Suzuki boundary Gram and of
arbitrary finite combinations of the complete arithmetic signals. The aim
is a global signed estimate for the Suzuki--Landau route. The estimate
itself remains open.

## What the audit found

Suzuki retains the full two-time kernel in equation (1.2). In section 3,
the zero-function orthogonality used to identify it with a positive
boundary Gram is proved under RH. His norm identity is an RH criterion,
not an unconditional arithmetic bound. This audit has not found an error
or an unnecessary loss of the full kernel in that argument.
See [Suzuki, The screw line of the Riemann zeta-function and its applications](https://arxiv.org/html/2209.04658v3#S3).

Within this repository, the optional
[absolute Schur estimate](../RiemannGaussian/RiemannXiSuzukiGramSchur.lean)
does discard mixed phases. The existing finite Gram and coefficient-tail
identities retain them. Neither a general Schur bound nor identification
of an infinite boundary synthesis with the arithmetic signal has been
assumed in the new theorems below.

## Exact carrier cancellation

Write `A(x)` for real-axis spectral xi, `E=A+i*A'`, and
`C=i*(1+E_sharp/E)/2`. Away from `E(x)=0`,

```text
C(x) = i*A(x)/(A(x)+i*A'(x)),
|C(x)|^2 = Im C(x),
conj(C(x))*C(x) = (C(x)-conj(C(x)))/(2*i).
```

`suzukiXiRealAxisCarrierDensity_eq_im` proves the circle identity.
At an exceptional denominator zero, the existing totalized definition
gives `C=i/2`, so the identity is false there: the squared norm is `1/4`
and the imaginary part is `1/2`. We do not change that definition.
`countable_suzukiXiEValue_real_zeros` proves all such points lie in the
countable genuine xi divisor; they therefore have zero Lebesgue measure.
The signed identity holds almost everywhere for the literal carrier.

For any two genuine spectral nodes `alpha_rho, alpha_sigma`,
`suzukiXiBoundaryCarrierGramKernel_eq_signed_integral` proves exactly

```text
H(rho,sigma) = integral_R
  (C(x)-conj(C(x))) /
    [2*i*(x-conj(alpha_rho))*(x-alpha_sigma)] dx.
```

The accompanying integrability theorem includes real and multiple nodes.
It uses the actual zero functions already proved to be in `L^2`, not a
claim that the separated rational factors are individually integrable.

## Complete arithmetic signals and arbitrary time tests

Let `P_t` be the repository's literal `riemannXiSuzukiArithmeticPPositive`,
with all pole, zeta, finite-prime, digamma and Lerch contributions. Its
unnormalized arithmetic signal is `S_t=C*P_t`. For every `t,u>0`,
`inner_suzukiArithmeticSignal_eq_phase_integral` proves

```text
<S_t,S_u> = integral_R
  [(C-conj C)/(2*i)] * conj(P_t) * P_u dx.
```

`integrable_suzukiArithmeticPhaseGramIntegrand` proves integrability of
the whole product. The equality also holds almost everywhere before
integration, so time couplings have not been compressed to norm bounds.

For every finite index type, arbitrary positive times `t_j`, and arbitrary
complex coefficients `a_j`, put `Q=sum_j a_j*P_(t_j)`. Then
`suzukiArithmetic_finite_phase_energy_eq_norm_sq` proves

```text
integral_R [(C-conj C)/(2*i)] * conj(Q) * Q dx
  = ||sum_j a_j*S_(t_j)||_2^2.
```

The combined integrand is genuinely integrable by
`integrable_suzukiArithmetic_finite_phase_energy`. This is a theorem for
all finite time tests of the actual arithmetic signal, with all cross
terms preserved. There is no coefficient search or orthogonality premise.

## What remains for the global bound

The circle identity replaces a quadratic carrier numerator with a signed
boundary difference. This opens a linear-carrier integral to analysis;
it does not reconstruct all of `C` from its squared norm, supply a new
arithmetic sign, or establish historical novelty.

At real divisor points the two channels can have singularities that only
cancel when kept together. Separate integration or contour deformation
needs its own proof, including real-node contributions and any poles of
`E` away from the axis. Zero-freeness of `E` in a half-plane is not an
available unconditional assumption.

The next useful estimate must control the signed discrepancy between the
actual arithmetic Gram and the screw kernel uniformly as time grows, or
directly prove the arithmetic floor in the
[balanced-cutoff reduction](suzuki-balanced-subpolynomial.md). Positivity
of the actual Gram alone does not identify it with the screw kernel. The
new identities prove no global zero exclusion and do not close RH.

The [local cancellation theorem](suzuki-carrier-local-cancellation.md)
now supplies the exact two-channel polar models at every genuine xi node,
including the reflected pairing and the actual small-circle integrals.
The possible carrier-denominator poles and global boundary estimates
remain separate obligations.
