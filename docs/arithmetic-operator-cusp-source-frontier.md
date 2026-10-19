# Source correction, integer row inversion, and the whole cusp gate

Local research checkpoint, 2026-10-19. This continues the
[common-base/section audit](arithmetic-operator-common-base-section.md)
and the [Siegel interpolation review](siegel-interpolation-review.md).
The strongest new result extends the **actual source Euler correction**
to every fixed half-plane strictly right of `2/3`. It does not extend
the detector estimate or the proved zero-free region.

## A proved extension of the unchanged source correction

[QuasiRHSourceHalfplaneAudit](../scripts/QuasiRHSourceHalfplaneAudit.lean)
works with the imported correction at its literal source coordinates
`w=1, z=1/6`. For a prime ideal of norm `q`, put

    e=q^(-1), D=eta(P)*q^(-s),
    R=A(P)*q^(3-6s),
    A(P)=conj(angularFactor(primary P))^6*eta(P)^6.

The checked exact local factor is

    H_P(s)=(1-e^2)*(1-(1-e)*D-e*R)/[(1-R)*(1-D)].

For every fixed `a>2/3`, Lean proves on `Re(s)>=a`

    |H_P(s)-1| <= 240*q^(-lambda(a)),
    lambda(a)=min(6*a-3,a+1,2)>1.

Unconditional ideal summability supplies a summable envelope. The terminal
theorems `exists_uniform_source_cutoff` and
`exists_source_nonvanishing_cutoff` produce a fixed integer cutoff `N`
such that, for every finite exclusion set containing the prime ideals of
norm at most `N`, and every native finite Hecke character, the **same**
`PrincipalSignalComparison.sourceCorrection` is analytic on `Re(s)>a`
and differs from one by at most `1/2` on `Re(s)>=a`. It is therefore
nonzero on that closed half-plane. The cutoff can depend on `a`, but not
on height or the character. It is fixed before the growing detector scale.
Analyticity near a boundary point uses a slightly smaller fixed `a`.

This discharges the source correction's own `7/8` restriction without a
zero hypothesis. The previous exclusion set is not asserted to suffice,
and other source-data obligations must still be retained after enlarging it.

## The next source boundary has an actual angular L-function

The same strict leaf proves the exact algebraic defect

    (1-R)*H_P-1
      =[-e^2+(e+e^2-e^3)*D-e*(1-e^2)*R]/(1-D).

An independently reviewed **paper-level** calculation shows that the
extracted product `J=product ((1-R)*H_P)` is analytic and nonzero on
`Re(s)>1/2`: its error exponents are `2, Re(s)+1, 6*Re(s)-2`.
The remaining Euler factor is the angular Hecke function

    H_S(s)=L_S(Psi,6*s-3)*J_S(s),
    Psi((a))=eta(a)^6*(embedding(a)/|embedding(a)|)^(-6).

This identity initially holds in absolute convergence, `Re(s)>2/3`.
Extending it further requires meromorphic continuation of the angular
L-function and a continued definition of `H`. It is not a pointwise
identity for a nonconvergent, totalized Lean `tprod`.

The imported `HeckeFamily.Character` contains finite residue characters;
it does not contain this nonzero infinity type. Its zero supremum cannot
exclude zeros of `L(Psi,6*rho-3)`. If continuation is supplied, the pole
order of `H/L_eta` at `rho` is governed by

    ord_rho(L_eta)-ord_(6*rho-3)(L_Psi).

For `Re(rho)>2/3`, the auxiliary argument has real part greater than one,
so Euler nonvanishing preserves the source. Below that frontier an actual
auxiliary zero could cancel it; neither existence nor exclusion of such
a cozero is proved here. See the pinned independent source-frontier review
for the primary angular-Hecke reference and the exact constants.

## Native cusp arithmetic is now exact, but source allocation is separate

[QuasiRHNativeCuspStabilizerAudit](../scripts/QuasiRHNativeCuspStabilizerAudit.lean)
proves the actual sextic symbol identity

    72 divides D-1, k divides D-1  ==> chi_D(k)=1.

It retains zero, bad and nonunit numerators through native factorization
and the actual period-72 correction. Consequently the literal
determinant-one cusp translation matrix has

    chi_(1+a*c*t)(-c^2*t)=1

when `t` belongs to `jointFixedModulus`. The elementary interpretation as
a conjugated translation and the infinite cusp/Fourier calculations
remain paper-level. No arbitrary phase or cubic substitute is used.

The reviewed whole-cusp calculation retains every original spectral
`I,J`, the cube `J^3`, marks, rays, calibration, prime powers, height and
cutoff. Its residual pairing is still the existing signed theta
covariance. A nonzero infinity constant does not prove that pairing is
nonzero, and the numerator-one `principalFreeRow` is not a cusp or a
spectral projection. The source variable, the two density variables,
and the physical Eisenstein parameter must not be identified.

There is a useful narrowing of the missing estimate. The imported
`LowPhysicalInverseBound.low_physical_inverse_normalized` already proves
the marked/all-cube inverse energy bound. `LowUnselectedMass` already
pays the remaining tuple mass. A new **actual full-D physical remainder**
estimate of size

    sum_(Nm in [aQ,bQ]) |E_sigma,Y,v(m)|^2
      << Q^(1+epsilon)*(1+|v|)^J

would combine with those existing bounds to give the whole LOW continuous
cost `Z^(17/96+O(epsilon))`. Comparing it to the source
`Z^(beta-11/16)` requires `beta>83/96`. This conditional comparison is
not a new estimate or exclusion.

The original principal exterior bounds are already proved in their stated
domain, but require `beta+e>=7/8` (strictly greater in the physical residue
theorem). Their rational scale savings persist formally; their correction,
window, height and contour hypotheses do not extend merely because
`H(s,1,1/6)` does. A common continuation/source identity and the complete
exterior/high-row control remain necessary. The finite cusp computation
does not allocate the entire reciprocal-L source to theta automatically.

## Row deconvolution exposes an integer constraint and a phase obstruction

[ArithmeticOperatorRowDeconvolutionAudit](../scripts/ArithmeticOperatorRowDeconvolutionAudit.lean)
proves for the actual cyclotomic rows `C_N(b)=product_(2<=d<=N) Phi_d(b)`
that signed integral row exponents give exactly

    product_N C_N(b)^a_N = product_d Phi_d(b)^beta_d,
    beta_d=sum_(N>=d) a_N.

This is a rational-unit identity, not automatic integer preservation.
The checked sixth-row quotient satisfies

    C_6/(C_2*C_3)=Phi_4*Phi_5*Phi_6/Phi_2,
    this is an integer iff b+1 divides 6.

At `b=3` it is `4235/2`. A reviewed resultant argument extends the
obstruction on paper: for a fixed finite signed exponent vector, any
negative exponent gives a nonconstant reduced denominator `B(b)` which
must divide a fixed nonzero resultant if the quotient is integral.
Thus integrality for unbounded bases forces every reduced exponent
nonnegative. Fixed bases with growing exponent vectors remain open.

Ordinary logarithmic row identities also fail to preserve the full
prime-depth phase automatically. At `b=2`, the quotient is the integer
`155`, with 3-adic valuation zero. The row valuations are respectively
`2,1,1`, giving the linear phased contribution `log(3)*(z^2-z)` rather
than zero, where `z=exp(-iy*log(3))`. Resetting depth loses information.

The finite linear prime trace itself still collapses to the weighted
shifted-divisor kernel

    beta_p+sum_(d|p-1,d>=2) phi(d)*beta_d.

The linked prime head is essential. This finite identity remains valid
for arbitrary complex prime weights, so row inversion alone supplies no
independent signed estimate. The common-integer integrality condition is
real additional structure, but no source-sensitive asymptotic gain has
yet been derived from it.

## Verification and decision

The [manifest](arithmetic-operator-cusp-source-frontier-gates.json) records
the exact strict producers, all-local standard-axiom audits, 15 namespace
linters per leaf, independent reviews, finite regressions and artifact
hashes. Prior checkpoints are preserved. These are local audit leaves;
no root registration, broad CI, commit or push is included.

The correction extension is genuine analytic progress. Automatic
cusp-to-source allocation and row inversion as an estimate are now
explicitly bounded in scope. The next substantive gate is the actual
full-D physical transfer with its source/exterior ledger, or an
independent estimate of the complete signed theta covariance. Neither
is supplied by these identities. The imported strict `Re(s)>7/8` result
and the count of eight Tier-1 families visited, none exhausted, are unchanged.
