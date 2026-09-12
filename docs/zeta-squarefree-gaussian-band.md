# Uniform squarefree arithmetic on the explicit Gaussian band

The actual quotient `Q(s)=zeta(s)/zeta(2*s)` now has a proved common
closed-disc radius and one bound uniform over an explicit two-sided
height domain. This reaches the original quadratic sieve, full logarithmic
divisor matrix and source normalization, including changing selected zeros.
The independently bounded quantity is the complete matrix with ordinary
primes included. The separate ordinary-prime tail still needs its signed
lower bound for the RH contradiction.

## Exact height transport

Set

```text
Y = { y : 500002 <= abs(y), log(2*abs(y)+5) <= 320000 },
r_* = 1 + 1/900000,       c_y = 3/2 + i*y.
```

A denominator zero encountered by `Q` on the full closed disc about `c_y`
must satisfy `abs(Im(rho)-2*y)<=2*r_*`. The theorem `window_heights`
places every such ordinate in the actual Gaussian band's domain:
`10^6<=abs(Im(rho))` and `log(abs(Im(rho))+2)<=320000`.
The [proved Gaussian margin](../RiemannGaussian/ZetaGaussianBandExclusion.lean)
then excludes the denominator zero. Both genuine poles are also excluded.
There is no requirement on unrelated lower zeros and no unevaluated height
threshold in this application.

`analyticOnNhd_response` proves analyticity on a neighbourhood of the
complete closed disc. The center domain is compact, and the union of its
closed discs is the continuous image of a compact product. The theorem
`exists_uniform_quotient_bound` supplies one finite bound on this whole
tube. Its value has not been numerically evaluated.

These declarations are in
[ZetaSquarefreeGaussianBand.lean](../RiemannGaussian/ZetaSquarefreeGaussianBand.lean).

## Signed estimate before bounding the prime sets

For every `y` in `Y`, every `0<r<=r_*`, every finite prime set `S`, every
valid squarefree divisibility mark `P` disjoint from `S`, and every
complex polynomial `p`, the actual marked response obeys

```text
norm(response(p,S,P,N,c_y))
  <= C * A(S,c_y,r) * r^(-N) * sum_k norm(p_k)*r^(-k).
```

The same `C` works for all these choices. The exact two-harmonic envelope
is retained:

```text
A(S,c,r) = max_(abs(s-c)<=r) exp(-Re(Phi(S,s))),
Phi(S,s) = sum_(a in S) a^(-s) - (1/2) sum_(a in S) a^(-2*s).
```

Thus the first and doubled prime phases remain linked with their actual
signs and damping. The estimate does not assume a uniform bound on this
envelope as `S` grows. The generic common-constant theorem is
`SquarefreeEulerPhase.exists_uniform_response_bound_of_analytic` in
[ZetaSquarefreeEulerPhaseBound.lean](../RiemannGaussian/ZetaSquarefreeEulerPhaseBound.lean).
The Gaussian-band theorem discharges its analytic and uniform-bound premises.

## A whole growing sieve and every divisor pair

For any growing prime ceiling `R_N` satisfying `sqrt(R_N)<=N/40`
eventually, one constant and one starting order work for every `y` in `Y`,
every prime subset below `R_N`, every natural mark and every polynomial.
The bare response has bound

```text
C * exp(-N/(20*log(R_N+2))) * sum_k norm(p_k).
```

The logarithmic response costs the additional factor `N+1` and the
weighted polynomial envelope

```text
E(p) = sum_k (k+1)*norm(p_k).
```

For arbitrary complex divisor families `w,v` on a finite set `T`, let
`M(w,T)=sum_(d in T) norm(w(d))`. The complete logarithmic correlation
`J_N` satisfies

```text
norm(J_N) <= C*(N+1)*exp(-N/(20*log(R_N+2)))
                 * E(p) * M(w,T) * M(v,T).
```

The exact convergent lcm expansion is used first. Both coefficient families
and every ordered pair are present. Their complex product is not replaced
by a squared absolute value in the underlying identity. The declarations
are `exists_uniform_sieve_bound`, `exists_uniform_log_bound` and
`exists_uniform_family_bound` in
[ZetaSquarefreeGaussianSieve.lean](../RiemannGaussian/ZetaSquarefreeGaussianSieve.lean).
The general actual-quotient transport also remains available in
[ZetaSquarefreeEulerQuadraticSieveDecay.lean](../RiemannGaussian/ZetaSquarefreeEulerQuadraticSieveDecay.lean).

## Uniformity for the original selected-zero normalization

The common ceiling

```text
Rbar_N = floor(N/40)^2
```

contains the original prime sieve of every hypothetical right-half zero.
This is proved with integer rounding retained. Its use removes any need
for the selected zero's own prime cutoff to grow when the zero changes
with `N`.

For `u=3/2-Re(rho)` and the original squared divisor cutoff,

```text
D <= floor(u^(-N/4))^2,
u^(N+1) * M(w,{1,...,D}) * M(v,{1,...,D}) <= 1
```

whenever both complex weight families have norm at most one.
The exact full-pair estimate is discharged from `u*q^4=1` with
`q=u^(-1/4)`. It is not an extra arithmetic premise in
`exists_uniform_normalized_matrix_bound`.

Define

```text
a_N = (N+1)*exp(-N/(20*log(Rbar_N+2))).
```

Lean proves `a_N -> 0`. The original complete normalized matrix satisfies

```text
norm(normalizedLogResponse(rho,p,N,D,w,v)) <= C*a_N*E(p).
```

Here **both `C` and the starting order are common to all eligible zeros
whose ordinates lie in `Y`**. The selected zero, cutoff, complex weights
and polynomial may all vary with `N`; a bounded `E(p_N)` gives decay.
`tendsto_moving_moebius_matrix` instantiates the literal Möbius weights
using their proved norm bound. The constants and starting order are finite
but have not been numerically evaluated.

## Remaining contradiction step

The separate [prime-tail chain](zeta-squarefree-euler-family-decay.md)
retains the exact cancellation between the large-prime composite response
and the ordinary-prime correction. For a fixed hypothetical right-half
zero, the ordinary-prime term tends to `-m_rho`, where `m_rho>=1`.

The remaining independent target is a fixed positive margin, for example
`Re(P_N)>=-1+epsilon` with `epsilon>0` on a cofinal subsequence. The new
uniform matrix bound controls one already decaying part of that identity;
it does not bound the isolated prime correction. Other estimates in the
full prime-tail chain still have their own parameter dependence.
The zero-free region has not been enlarged by this slice, and RH remains
open. No historical novelty claim is made for compactness or Cauchy transport.

## Local validation

All four affected modules pass direct elaboration with warnings treated as
errors. The focused build passes 5,029 jobs and the full package build passes
10,350. Root verbose lint reports zero errors in 19,904 declarations plus
11,659 generated declarations, with all 14 linters. All 40 public theorems
in the affected modules have explicit transitive axiom audits containing
only `propext`, `Classical.choice` and `Quot.sound`.

The inventory contains 1,503 project modules, 31,602 declarations and 27,733
theorems, with no project axioms, placeholder dependencies or nonstandard
transitive theorem axioms. `rhImplied` remains false. These are local checks;
this continuation has not been committed or remotely verified.
