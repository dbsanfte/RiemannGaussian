# The complete Euler correction: even integral and odd energy

[Explore both correction bounds and the retained coupling](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=euler-correction-decay).

Lean now factors the full finite prime character into an explicit Euler
quotient and its correction, then pays **every interaction order** of that
correction. The even paired quotient has a vanishing integrated allowance;
the odd channel has a vanishing energy allowance. Both are uniform in finite
prime selections and height on each fixed closed half-plane right of one
half. **The independent floor for the original signed tail remains open.**

## An exact finite factorization

For a local complex weight `q`, unit character `z`, and `|q|<=1/4`, put

```text
w(q,z) = q^2 (z-1)/(1-q*z).
1+q(1-z) = ((1-q*z)/(1-q)) (1+w(q,z)).
```

All denominators are separated from zero: `|1-q*z|>=3/4`. For a finite
selection `Q`, set `q_p=p^(-s)`, `ell_p=log p`, and `z_p=exp(i ell_p xi)`.
The complete character is exactly

```text
prod_Q [1+q_p(1-z_p)] = G_Q(xi) H_Q(xi),
G_Q(xi) = prod_Q (1-q_p*z_p) / prod_Q (1-q_p),
H_Q(xi) = prod_Q [1+w(q_p,z_p)].
```

The theorem applies to literal prime features at labels at least 16 for
`Re(s)>=1/2`. This is a **finite** Euler quotient identity. Passage to an
infinite quotient of zeta functions is not asserted here. Small primes and
the original completed-minus-boundary restriction remain explicit upstream.

## Pair before dividing by frequency squared

Each local correction has a linear term at frequency zero. Its reciprocal
pair has the exact second difference

```text
w(q,z)+w(q,z^-1)
 = q^2(1+q)(z+z^-1-2)/[(1-q*z)(1-q*z^-1)].
```

Thus the paired integral costs at most `8 pi |q|^2 |ell|`. No separate
integrability claim is made for the unpaired correction divided by `xi^2`.
The next estimates cover the full product, including all higher prime
interactions, rather than stopping at the sum of local corrections.

Define

```text
M = sum_Q |q_p|^2,
J = sum_Q |q_p|^2 |ell_p|,
E_Q(xi) = sum_Q |q_p|^2 (1-cos(ell_p*xi))/xi^2,
C = 2+exp(8M).
```

The energy is nonnegative and integrable, with `integral E_Q=(pi/2)J`.
Writing `T_Q=sum_Q log(1+w(q_p,z_p))`, Lean proves `H_Q=exp(T_Q)` with all
local logarithms justified, and

```text
|T_Q(xi)| <= 8M,
|T_Q(xi)|^2/xi^2 <= 32M E_Q(xi).
```

Weighted Cauchy--Schwarz keeps the square-amplitude mass `M`; the bound does
not acquire a factor counting the participating primes. Pairing the linear
terms and bounding both quadratic exponential remainders gives

```text
integral_0^infinity |H_Q(xi)+H_Q(-xi)-2|/xi^2 dxi
 <= (32+64M C) (pi/2) J,

integral_0^infinity |H_Q(xi)-H_Q(-xi)|^2/xi^2 dxi
 <= 128 C^2 M (pi/2) J.
```

Both are ordinary integrals with integrability proved. The odd channel is
retained alongside the even one, so subsequent multiplication can use its
correlations rather than dropping it.

## Uniform arithmetic decay

Fix `sigma>1/2`. For every `s` with `Re(s)>=sigma`, and every finite prime
selection above `max(16,K)`, replace `M` in the constants by the convergent
integer majorant `M_sigma=sum_n zetaPrimeExpWeight(2sigma,n)`. Replace `J`
by the existing `squareLogTail sigma K`, which tends to zero.

The two `exists_uniform_actual_*` endpoints prove the quantifiers: one
threshold works for **all** such finite selections and **all** points in the
closed half-plane. Constants may depend on `sigma`; no uniform limit as
`sigma` approaches one half or numerical threshold is asserted.

## What restoring the leading response requires

For arbitrary complex leading responses `V+`, `V-`, Lean retains exactly

```text
V+(H+-1)+V-(H--1)
 = ((V++V-)/2)(H++H--2) + ((V+-V-)/2)(H+-H-).
```

The first term uses the controlled even correction. The second uses the
controlled odd energy and still needs information about the odd leading
response. Unweighted correction decay does not pay either leading factor.

| Component | Checked control | Still needed |
| --- | --- | --- |
| Full even Euler correction | Uniform vanishing integrated allowance | Its coupling to the even leading response |
| Full odd Euler correction | Uniform vanishing energy allowance | Its coupling to the odd leading response |
| Finite leading Euler quotient | Exact factorization, every prime phase retained | An estimate compatible with the source scale |
| Physical cutoff, fixed factorial filter and signed boundary | Preserved in the original carrier chain | Transport and bound the full coupled expression |
| Semiprimes and larger composite cofactors | Their joint source remains after the proved cofactor deletions | The independent cofinal real floor strictly above minus one |

No RH proof, new zero-free region, numerical certificate or historical
novelty is claimed. The correction estimates are supporting components of
the [original signed-tail campaign](zeta-riesz-signed-fourier-tail.md).

## Checked sources and audits

[ZetaRieszEulerQuotient](../RiemannGaussian/ZetaRieszEulerQuotient.lean)
contains 18 declarations; [ZetaRieszEulerCorrectionEnergy](../RiemannGaussian/ZetaRieszEulerCorrectionEnergy.lean)
contains 34. Both are in the ordinary root. The
[explorer audit](rh-proof-explorer/audit.json) exposes compiled statements,
dependency paths, exact source lines and transitive axiom checks. The main
endpoints are `exists_uniform_actual_paired_correctionProduct_lt`,
`exists_uniform_actual_odd_correctionProduct_energy_lt`, and
`weighted_correction_pair_split`. The default whole-carrier endpoint remains
`ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
