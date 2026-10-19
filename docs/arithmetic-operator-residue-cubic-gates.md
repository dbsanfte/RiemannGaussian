# Global square-sector arithmetic and source gates

2026-10-19. Local research following the Banks interpolation review. The
new positive candidate uses an actual cubic large sieve on the original
finite sextic Gauss sums. Its complete application is still being
formalized. The separate residue argument is a reviewed paper proof,
conditional on the recorded physical identification when used in the
campaign. Neither assigns the hypothetical-zero source to the square
sector or proves a new zero-free region.

## The useful arithmetic distinction

The earlier square-core countermodel satisfies the tested local Hecke
relations and a global positive energy bound. It is not automorphic and
does not satisfy the actual residue functional equation. It therefore
does not refute an estimate using that additional global equation.

There is also a shorter route: for a square numerator, the varying sextic
character becomes a cubic character. The imported library already proves
the sharp arithmetic cubic sieve. Applying that theorem to the original
finite amplitude avoids any residue-contour identification.

The relevant vector must be common to all rows in each sieve application.
The new strict leaf
[QuasiRHSquareCubicMeanAudit.lean](../scripts/QuasiRHSquareCubicMeanAudit.lean)
retains arbitrary fixed complex coefficients, separate row and column
contractions, and the character's literal nonunit zeros. It proves

    sum_i |r_i sum_j cubicRow(j,i) c_j b_j|^2
      <= C_e (MN)^e [M+N+(MN)^(2/3)] sum_j |b_j|^2.

This is an application of the actual imported cubic sieve, not a generic
matrix norm or an assumed arithmetic estimate. Arbitrary masks depending
jointly on both indices are not licensed.

## Direct finite amplitude: the promising application

The original `lowRayAmplitude` is a finite Gauss polynomial with the
single column vector `lowGaussColumn`, whose entries are bounded by
`C_W/Y`. This retains the ray, calibration, current exclusions, physical
window and height phase.

For a supported squarefree root `a` and unit `zeta`, put `m=zeta*a^2`.
The exact prime-power support forces every nonzero physical modulus to be

    c=b*d^3,  d|a,  b,d squarefree,  (b,a)=1.

In particular the physical moduli are not restricted to squarefree
ones. The prime-cube moduli are essential. For each fixed `d`, writing
`a=d*v` gives the actual normalized Gauss row as

    G(b*d^3,-zeta*d^2*v^2)
      = Nd * F_zeta(b,d) * conjugate(cubicRow(b,v)),

with the full CRT factor retained and `|F_zeta(b,d)|=1`. The remaining
coprimality and physical masks are separate row/column restrictions or
the cubic character's own zero extension. The fixed-`d` column energy is
`O(1/(Y*Nd))`. The sharp cubic sieve then gives the paper block bound

    (AY)^e [A/(Y*D^2) + D^(-4)
                     + A^(2/3)*Y^(-1/3)*D^(-11/3)],  D=Nd.

Divisor Cauchy, the actual ideal divisor bound, and convergent ideal norm
sums assemble these blocks. There is no free interchange of a squared
sum with a sum of squares. The resulting reviewed paper estimate is

    sum_(a squarefree, Na<=A) |lowRayAmplitude(zeta*a^2)|^2
      << (AY)^e [1+A/Y+A^(2/3)*Y^(-1/3)].

With `A=sqrt(Q)`, `Q=Z^(5/6-2d)` and `Y=Z^(23/48-d)`, its native cost is

    Z^(17/288-d/6+O(e)),  0<=d<=1/6.

This pays a sector once the finite bridge and assembly are formalized.
It does not bound the complete amplitude by deleting the other numerator
sectors. The independent preflight is in
`.lake/arithmetic-operator-direct-square-amplitude-independent/`;
the primary derivation is in
`.lake/arithmetic-operator-direct-square-amplitude-preflight/`.

For arbitrary roots but squarefree physical moduli, the imported full
element cubic bound instead gives energy
`(AY)^e[A^(1/3)+A^(4/3)/Y]`. That is a separate restricted-column result,
not a bound for their sum with the imprimitive columns. For repeated-root
prime factors, physical exponents five, six and larger can survive.
Those cases require their own exact decomposition. The subsequent audit
below supplies a paper candidate for precisely that missing decomposition.

## All square roots and all physical moduli

A further local classification and independent review extend the paper
argument without using a theta residue. Every surviving modulus has the
unique form

    c=H^6*b*d^3*e^5,   T=H^3*d*e^2,   x=T*v,

where `b,d,e` are squarefree and pairwise coprime. `H` can overlap all
three. For the actual normalized Gauss sum the exact proposed bridge is

    G(c,-zeta*T^2*v^2)
      = G(c,-zeta*T^2) * conjugate(cubicRow(b,v))
                          * cubicRow(e,v) * 1_((v,d)=1),
    |G(c,-zeta*T^2)| <= NT.

There is **no** condition `(v,H)=1`. A prime occurring only in `H` has a
principal Ramanujan branch already constant at this numerator valuation,
including when it divides `v`. A prime also in `b,d,e` is handled by the
corresponding cubic zero or explicit `d` condition. These distinctions
prevent the accidental deletion of genuine imprimitive terms.

Fixing `H,d,e` leaves one column vector over `b`. All remaining factors
are bounded row contractions. The actual full-element cubic sieve can
therefore use arbitrary nonzero roots, not just squarefree roots. Its
row and column scales are

    U=A/(H^3*d*e^2),   B=Y/(H^6*d^3*e^5),

where symbols in this rate display denote ideal norms. The column energy
is bounded by `C/(Y*d*e)`. This gives the two block costs

    A^(1/3)*H^(-7)*d^(-13/3)*e^(-20/3),
    A^(4/3)/Y*H^(-4)*d^(-7/3)*e^(-11/3).

There is a simpler one-divisor organization. `T` uniquely determines
`H,d,e` by the valuations modulo three, and every active `T` divides
`x`. Since `H^6*d^3*e^5=T^2*d*e`, the costs are at most

    A^(1/3)*T^(-7/3) + A^(4/3)/Y*T^(-4/3).

Both ideal sums converge. Divisor Cauchy costs only a small power of `A`.
The resulting **paper** all-square estimate is

    sum_(0<Nx<=A) |lowRayAmplitude(zeta*x^2)|^2
      << (AY)^e [A^(1/3)+A^(4/3)/Y].

It has native cost `Z^(5/72-d/6+O(e))`, with no adverse unselected-length
power. The physical window is scaled by its actual fixed upper support
endpoint; a subunit block is empty unless that endpoint allows it. No
column or root is removed without its exact local support condition.

The strict local leaf
[QuasiRHFiniteSquareGaussAudit.lean](../scripts/QuasiRHFiniteSquareGaussAudit.lean)
now proves the actual squarefree-root support, the full principal and
nonprincipal valuation table, and exact square-unit invariance at cube
moduli. It does not yet prove the global all-nonunit CRT bridge above.

The strict energy leaf
[QuasiRHFiniteSquareEnergyAudit.lean](../scripts/QuasiRHFiniteSquareEnergyAudit.lean)
proves the squarefree-root cubic divisor assembly and the norm of the
literal `lowGaussColumn`, then gives an explicit implication to the
original amplitude from the displayed finite Gauss bridge. The energy
is derived from the imported cubic sieve; it is not a hypothesis. The
bridge itself remains a hypothesis. The same leaf proves the actual
full-element cubic input needed for arbitrary roots. It does not yet
assemble the whole all-square estimate into an unconditional Lean
endpoint. The complete paper audit is frozen in
`.lake/arithmetic-operator-all-square-amplitude-gate/`.

This application is not a newly invented source detector. It estimates
an exact sector of the original carrier, whose total source was already
identified. No nonzero source is assumed for that sector. The sieve
permits arbitrary common column weights, but requires the actual cubic
character matrix: replacing its rows by arbitrary coherent data does
not preserve the theorem. Thus the estimate uses additional arithmetic
information beyond the local equations in the earlier countermodel.

## Global residue route: stronger scope, a longer formal bridge

Using the exact Broeker--Hoffstein contour and full functional equation,
with the actual raw normalization, the reviewed paper argument gives

    sum_(Na~A, a squarefree, (a,6M)=1)
      |rho_nu(-M*a^2)|^2 <<_(M,nu,e) A^(1+e).

Here `M` and the finite section are fixed. The raw normalization is
`Na^(-1/6)`. All nonzero good moduli, fixed bad factors, moving smooth
kernels and completion indices remain. Mellin separation gives one
column vector per sieve application. Minkowski retains the harmonic/log
cost of the completion sums; it is not a free square summation.

The actual finite-vector exponent-four exchange and sixth-power
periodicity then give raw all-even-valuation energy `Q^(1/2+e)`.
The corresponding native cost, conditional on the prior physical residue
bridge, is

    Q^(1/4)*Y^(-1/3) = Z^(7/144-d/6).

[QuasiRHSquareEnergyRateAudit.lean](../scripts/QuasiRHSquareEnergyRateAudit.lean)
checks this rate and the exact available margin. It does not prove the
residue estimate. In fact an energy saving of only
`eta > 156/625000` from the old exponent `5/6`, before other losses,
would suffice for this sector at the current target endpoint. The
candidate `1/2` exponent leaves much more room.

The primary and independent reviews are frozen in
`.lake/arithmetic-operator-global-square-identity-gate/` and
`.lake/arithmetic-operator-global-square-independent-review/`.
The [Broeker--Hoffstein equations](https://arxiv.org/abs/1312.0568v1)
used here are proved analytic identities, not the later conjectural
coefficient formulas. The
[Heath-Brown cubic sieve](https://ora.ox.ac.uk/objects/uuid:16c3966e-61cb-499d-839c-559b3794fcff)
is already available in the native Lean import.

## Two additional common-integer source tests

The strict leaf
[ArithmeticOperatorAdditiveCommonSourceAudit.lean](../scripts/ArithmeticOperatorAdditiveCommonSourceAudit.lean)
tests addition before common divisibility. For actual cyclotomic cutoff
products `C_N`, positive `h`, and every physical depth `p^r<=N`, away from
the base primes,

    p^r | gcd(C_N(b), C_N(c)+h) iff p does not divide b and p^r | h.

At a base prime dividing `c`, the prime-level condition instead uses
`p | h+1`; all exceptional depths remain explicit. Every complex depth
weight is retained. A polynomially growing positive lag therefore loses
every positive-power source in the saturated physical window. The
unsaturated window remains a separate source question. The usual theorem
for one fixed finitely generated S-unit group does not apply to these
cutoff products: their prime support keeps growing.

The Wilson-quotient test, modulo `n^2`, is separate from the earlier
smooth Wilson-code no-go. The exact paper decomposition has the form

    T_h(s)=D_h(s)+A_h(s)D_0(s)+B_h(s)D_chi4(s)+E_h(s),
    D_h(s)=sum_p log(p) exp(2*pi*i*h*W_p/p) p^(-s).

The ordinary-prime coefficient can be nonzero, but the residue of the
total expression is unknown: the `D_h` channel might cancel it. Known
Fermat-quotient exponential-sum bounds do not supply that residue;
Lerch's identity gives a product of phases, not the needed sum. This
branch stops at its source test. No new Lean Wilson-quotient theorem or
counterexample to its possible future usefulness is claimed.

## Status and next obligation

The strict leaves in this checkpoint use all-local provenance, standard
axioms only, and all 15 namespace linters. The companion JSON records
their exact counts and separates those results from
the reviewed paper estimates and conditional campaign applications.
Numerical regressions test finite algebra and rational exponents only.

The next useful task is to close the direct **actual finite** all-square
Gauss bridge and apply the proved cubic input and divisor estimates.
The precise all-nonunit identity above is the remaining formal bridge;
it cannot be replaced by a freely chosen phase or an energy assumption.
Prime and odd-core covariance remain unpaid. Source belongs
to the original full carrier, not to a selected sector. The imported
strict `Re(s)>7/8` region and the prior full-central saving remain
unchanged. Eight Tier-1 families have been visited; none is declared
exhausted. Work remains local, with no broad CI, publication or push.
