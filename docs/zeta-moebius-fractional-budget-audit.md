# The source-scale obstruction to the fractional absolute-kernel estimate

The fractional arithmetic modulus is valid, but its accompanying absolute
kernel budget cannot close the signed RH target. Lean now proves that this
budget, multiplied by the selected-zero normalization, tends to infinity.
This holds for every fixed polynomial preserving the selected scale and,
for the actual pole-jet filters, even for moving fractional exponents up to
and including one quarter.

This is a method obstruction, not a zero exclusion. The full signed
Möbius interaction remains available and its independent lower bound remains
open. The theorem rules out a fixed source-beating ceiling from this norm
estimate, so the issue is stronger than failure to prove a power saving.

The terminal theorems are
`tendsto_zetaRightHalf_resonantFractionalMass_atTop` and
`tendsto_zetaRightHalf_resonantFractionalMass_moving_atTop`; the complete
allowance is covered by `tendsto_zetaRightHalf_centeredFractionalAllowance_atTop` in
[ZetaMoebiusFractionalBudgetAudit.lean](../RiemannGaussian/ZetaMoebiusFractionalBudgetAudit.lean).

## The quantity tested

Keep the actual finite cyclic samples from the
[centered resonance theorem](zeta-moebius-centered-resonance.md):

```text
q_N = 2^(32*N)+1,
f_N(j) = K_p,N(1/4+i*y,j) for j>0, f_N(0)=0,
F_N = DFT(f_N),
lambda(k) = exp(2*pi*i*k/q_N)-1,
S_N = {k : |lambda(k)| < delta_N},  delta_N=(31/32)^N.
```

Define the normalized fractional absolute mass on a frequency region `S`:

```text
W_N(tau,S) = (1/q_N) sum_{k in S} |lambda(k)|^tau * |F_N(k)|.
```

The preceding arithmetic modulus gave the genuine bound

```text
|C_N| <= 2*H(5/4-tau)*W_N(tau,S_N),    0<=tau<1/4,
```

where `C_N` is the complete centered signed interaction and `H` is the
convergent positive divisor-majorant mass. The new calculation tests
`W_N` independently of the signed arithmetic source limit.

## Fourier inversion supplies physical tests

[FiniteFourierFractionalBudget.lean](../RiemannGaussian/FiniteFourierFractionalBudget.lean)
retains the exact inverse formula

```text
f(j)-f(0) = (1/q) sum_k [exp(2*pi*i*k*j/q)-1]*DFT(f)(k).
```

For `0<=tau<=1`, the previously proved unit-phase inequality yields

```text
|f(j)-f(0)| <= 2*j^tau*W(tau,all frequencies).
```

Thus an absolute Fourier budget must be large enough to recover individual
physical samples. The same module proves the complementary bound

```text
W(tau,S) <= 2*delta^(-r)*sum_j |Delta^r f(j)|
```

when every frequency in `S` has symbol norm at least `delta>0`.
The normalizing group size cancels exactly; all physical cyclic differences
and their boundary terms remain included.

## The finite samples control the whole continuous kernel

[ZetaQuarterKernelFourierBudget.lean](../RiemannGaussian/ZetaQuarterKernelFourierBudget.lean)
proves a first-derivative bound uniform over all moment orders and `x>=1`:

```text
|K_p,N+1'(1/4+i*y,x)| <= A(p,y),
A(p,y) = (1+|1/4+i*y|)*sum_k |p_k|.
```

The complete lowering derivative is retained before applying the bound.
Rounding `x` down to its natural floor therefore costs at most `A(p,y)`
for positive moment orders. Below the finite endpoint, Fourier inversion
controls the rounded sample. Beyond the endpoint, the existing upper-tail
bound applies to every real `x` in that region.

With `P_8(p)=sum_k |p_k|*8^k`, set

```text
J(p,y) = A(p,y)+2*P_8(p).
```

For every `N>=1`, `x>=1`, and `0<=tau<=1`, Lean proves

```text
|K_p,N(1/4+i*y,x)|
 <= 2*x^tau*W_N(tau,all frequencies)+J(p,y).
```

The constant is independent of `N`. There is no unproved interpolation
assumption, omitted integer boundary, or infinite Fourier interchange.

## Exact Laplace tests keep the polynomial coupled

Write

```text
P_N(t) = sum_k p_k*t^(N+k)/(N+k)!.
```

[ZetaPrimeKernelLaplace.lean](../RiemannGaussian/ZetaPrimeKernelLaplace.lean)
proves genuine integrability and the exact complex identity, for every `d>0`:

```text
integral_0^infinity P_N(t)*exp(-d*t) dt
 = d^(-N-1)*p(1/d).
```

The proof evaluates each convergent factorial Gamma integral and reassembles
the finite polynomial. The resulting evaluation retains all complex
coefficients together.

Apply the continuous kernel bound at `x=exp(t)`, then integrate against the
remaining positive damping. For `d>1/4+tau`, this gives

```text
d^(-N-1)*|p(1/d)|
 <= [2/(d-1/4-tau)]*W_N(tau,all frequencies)
    + J(p,y)/(d-1/4).
```

This is the quantitative theorem
`zetaQuarterKernel_laplace_le_fractionalFourierMass`. Both exponent gaps
are positive, and the comparison integrals are proved integrable.

## Why the available exponents cannot close the bound

Let `u` be the normalization scale, with

```text
1/4+tau < u < 1,  and p(1/u) != 0.
```

Continuity of the full polynomial evaluation gives some
`d` strictly between `1/4+tau` and `u` with `p(1/d)!=0`.
After multiplying the preceding inequality by `u^(N+1)`, its left side is

```text
(u/d)^(N+1)*|p(1/d)| -> infinity,
```

while the fixed interpolation term tends to zero. Therefore

```text
u^(N+1)*W_N(tau,all frequencies) -> infinity.
```

This is proved for every fixed polynomial with nonzero evaluation at the
selected scale. It does not assume a hypothetical zero or use a limit of
the Möbius arithmetic sum.

The complementary fractional mass independently tends to zero by the
complete second-difference estimate. Consequently the divergence occurs
inside the same shrinking resonant region:

```text
u^(N+1)*W_N(tau,S_N) -> infinity.
```

For every hypothetical right-half zero `rho=beta+i*gamma`, the actual
pole-jet filter satisfies `p(1/u)=1` exactly, where `u=3/2-beta`.
The condition becomes

```text
0<=tau<5/4-beta.
```

Since every such zero has `beta<1`, the exponent `tau=1/4` itself lies
strictly below this threshold. On `S_N` the symbol norm is at most one, so
the absolute mass decreases as its nonnegative exponent increases. Thus
for **any** moving sequence `0<=tau_N<=1/4`,

```text
u^(N+1)*W_N(tau_N,S_N) -> infinity.
```

This covers approaching the endpoint as `N` grows. The result concerns
fixed polynomials; it does not assert uniformity over polynomials or
ordinates varying without a common budget.

The arithmetic prefactor cannot undo this growth. Its actual convergent
majorant satisfies the uniform positive floor

```text
H(5/4-tau) >= log(2)*exp(-(5/4)*log(2)) > 0,    0<=tau<1/4.
```

Lean therefore also proves divergence of the **complete** normalized
allowance `u^(N+1)*2*H(5/4-tau_N)*W_N(tau_N,S_N)` for every moving
admissible sequence `0<=tau_N<1/4`. The endpoint `tau=1/4` is used only
for the kernel comparison; no convergence of the arithmetic majorant at
that endpoint is asserted.

## Consequence for the active goal

The checked arithmetic modulus currently supplies exponents below `1/4`.
Every corresponding absolute kernel mass diverges at the source scale.
Changing the fixed source-preserving polynomial or choosing a moving
exponent through `1/4` cannot repair this particular estimate.

The new theorem locates the information that this route must retain:
the cancellation between the centered arithmetic increment and the kernel
inside their full signed Fourier products. It does not prove that no other
norm argument could work. Nor does reaching the threshold `5/4-beta`
establish sufficiency; the theorem proves failure strictly below it.

The original target is unchanged: for every selected right-half zero,
prove an independent signed inequality beating the normalized negative
multiplicity by more than the proved error, at arbitrarily late orders.
The centered source identity and the complementary decay remain valid.
The next arithmetic estimate must use more information than the current
fractional modulus followed by an absolute kernel sum.

## Validation and status

The four modules are imported from the project root. Local verification uses
warnings as errors, focused and full builds, all declaration linters,
terminal axiom audits, the complete source scan, and deterministic inventory
generation. Allowed dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. Commits and remote CI remain held.

The existing centered-source inventory milestone is retained. This audit
does not advance the zero bound or create a completed RH milestone. No
mathematical-priority claim is made for the Fourier or Laplace mechanisms.
