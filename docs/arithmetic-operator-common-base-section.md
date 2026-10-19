# Common-base correlation, moving norms, and the literal sextic section

Local research checkpoint, 2026-10-19. This continues the
[total-source audit](arithmetic-operator-total-source-section.md) and the
[Siegel interpolation review](siegel-interpolation-review.md). Four strict
Lean leaves resolve finite arithmetic questions; the infinite analytic
claims below are explicitly paper-level. No new independent signed RH
estimate or zero-free region is claimed.

## One common base: complete averaging deletes the distinct-prime correlation

For the actual integer polynomial

    C_N(b)=product_(2<=n<=N) Phi_n(b),

let I_(p,r)(b) indicate p^r dividing C_N(b). Use ONE integer b throughout,
not independently chosen residues disguised as a common base. CRT gives,
on a complete common period and for distinct primes p,q,

    E[I_(p,r) I_(q,s)] = E[I_(p,r)] E[I_(q,s)].

[ArithmeticOperatorCommonBaseCRTAudit](../scripts/ArithmeticOperatorCommonBaseCRTAudit.lean)
proves this for the literal polynomial, with a legal common integer
representative >=2, and proves zero centered covariance with arbitrary
complex weights. It also retains the nesting of prime-power incidences
and excludes primes dividing the base.

At one prime the events are nested, so their covariance is
`mu_(p,max(r,s))-mu_(p,r)*mu_(p,s)`. The paper-level full variance formula
therefore consists entirely of these same-prime blocks. For literal
weights `log(p)*p^(-i*r*y)`, the Hermitian prime-only diagonal loses y;
the higher-depth part is bounded by the previously paid proper-power
trace, with an extra logarithm. This does not bound the original mean.
The non-Hermitian square retains the prime phase at 2y; its unsaturated
diagonal remains an unpaid scalar arithmetic trace. It is not declared
source-free merely because the Hermitian diagonal is height-independent.

Incomplete base intervals are different. The exact example N=2, p=2,
q=3, B=2, H=1 has centered covariance -1/3. Complete averaging cannot
replace it for free. The explicit finite-interval error and the common
base's height remain in the ledger. Thus this result freezes only the
complete-average covariance shortcut; it does not rule out a new
moderate-height common-base constraint.

## A moving algebraic base retains divisor arithmetic, but not this zero source

Take alpha_N=2^(1/N) and the complete algebraic norm of the preceding
rank-N boxed determinant. All N conjugates are included. The independently
reviewed paper calculation gives

    log |Norm D_N(alpha_N)|=((3N^3-N^2)/2)*log 2+F_N,
    F_N=sum_(d|N) (N/d)^2*c_d.

Here c_d is the exact positive coprime tent sum

    sum_(1<=k<2d,(k,d)=1) min(k,2d-k)
      *[log(1-2^(-d-k))-log(1-2^(-k))].

[ArithmeticOperatorRadicalQBoxAudit](../scripts/ArithmeticOperatorRadicalQBoxAudit.lean)
proves the finite gcd-fiber/divisor reindexing, first for arbitrary row
data and then for this literal logarithmic profile. It identifies c_d
with the exact function in
[ArithmeticOperatorRadicalQBoxTailAudit](../scripts/ArithmeticOperatorRadicalQBoxTailAudit.lean),
which proves

    0 <= B_d-c_d <= 16*(d+1)*2^(-d),
    B_d=sum_(k>=1,(k,d)=1) k*(-log(1-2^(-k))).

Every polynomial absolute moment of this deficit is also summable.
The field-norm and determinant identification itself is paper-level;
the finite profile is not substituted for that missing formal theorem.

On paper these exact formulas yield

    sum_N F_N*N^(-s) = zeta(s-2)*(zeta(s)*H(s)+E(s)),

where H and E are entire. The raw ordinary row Dirichlet transform has
possible poles only at 4,3,1, and is holomorphic at every nontrivial
zeta zero. Unlike the fixed-base residual, F_N genuinely retains divisor
oscillations; nevertheless this observable fails the zero-source gate.
The conclusion does not cover phased valuations, Mobius-deconvolved
rows, other determinant geometry, or incomplete conjugate observations.

## The native sextic section can use the literal coefficient directly

The positive applicability result uses the actual
`ProbeGramCommon.primaryCoefficient S hS sigma c`, including calibration,
primary selection, physical ray and all fixed exclusions. There is no
replacement by the principal or imported cubic profile.

[QuasiRHNativeSectionLiftAudit](../scripts/QuasiRHNativeSectionLiftAudit.lean)
proves the primitive-row bijection under SL2 of the Eisenstein integers,
the actual coefficient's invariance under the fixed-level first-column
congruences, and both zero-coordinate omission checks. The last point
matters: the nonzero-c row set is not invariant, but all rows can be
reindexed before zero-weight rows are removed.

An independently reviewed paper derivation establishes the actual sextic
row law, the local lift at the explicit level, and the Fourier constants
for the section

    sum_((c,d) primitive) h(c)*chi_c(d)
      *y^u/(|cz+d|^2+|c|^2*y^2)^u.

It retains nonunit numerators, every prime-power modulus, and the unique
primary generator rather than adding a spurious factor six. The native
pairing has covolume sqrt(3)/2, and the physical coefficient is at -m.
This construction avoids the intermediate good-prime numerator extraction
operator; its earlier audit remains valid within its scope.

The full automorphy, Fourier unfolding and continuation are paper-level,
not new Lean theorems. The explicit local Hensel calculation at the prime
over 3 is needed: applying strict Hensel at 1 at the equality threshold
would be invalid. The reviewed calculation corrects the approximate root
before applying it.

The sigma=1 section has a nonzero outgoing infinity residue on paper.
This is not the original physical zero-frequency term, which is excluded,
and does not identify the original detector source with a particular pole.
The whole transformed-cusp/scattering vector, spectral marks and moving
profiles must still be joined to prove that source identity. Its signed
covariance estimate is a further independent obligation.

Scalar Laplace/heat or scalar Hecke filtering of the residual theta
eigenspace only rescales or kills its entire covariance and source.
The paper-level filter audit therefore freezes that shortcut. A genuine
finite cusp-matrix interaction remains a separate question requiring the
actual scattering data and source vector, not an assumed projection.

## Validation and next decision

The [checkpoint manifest](arithmetic-operator-common-base-section-gates.json)
records four strict leaves: 98 module-local declarations, including
76 theorem declarations and generated helpers; 15 namespace linters per
leaf and only standard axioms. The root reran every producer in dependency
order. Exact finite probes passed 1,911 common-base cases, 156 individual
radical norms plus four whole determinants, and 42 actual native row-law
cases. These regressions are not analytic source proofs.

All 337 preceding artifact pins and 68 additional agent pins matched
before shared notes changed. Local work only: no root registration,
broad CI, commit or push. The active goal remains eight Tier-1 families
visited and none exhausted; the imported strict Re(s)>7/8 boundary is
unchanged.

The next source-sensitive task is the whole native transformed-cusp
residue pairing. It must retain the reciprocal-L source, fixed
calibration, spectral I/J and cube conditions, marked primes, phases,
and moving cutoff simultaneously. Section existence alone supplies no
signed estimate. If the actual paired identity still reduces to the
unpaid scalar trace, record that reduction before another estimate.
