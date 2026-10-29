# Fast tag-readout tests: rational blocks, paired inverses and summation

26 October 2026. The [preceding packet](../semiprime-projective-readout-20261026/README.md)
paid the projective starting data and licensed pure K=2*3^e preparation.
This pass executes the next proposed algorithms rather than counting
another recurrence as a fast evaluation.

**No whole-query speedup was obtained.** There is a new conditional
degree theorem for the actual tag-ratio block, paid cross-family inverses
and projectors, and a two-endpoint screening theorem for bounded rational
q-Gosper certificates. These distinguish viable remaining scalar-evaluation
questions from specific proposed shortcuts that do not supply them.
The best completed native weighted query remains soft K^(5/4); the
two-monic first-jet fallback remains soft K^(3/2). The full deterministic
all-semiprime sixth-exponent goal and its bit-complexity proof remain open.

## 1. The actual initialized readout

Use the prepared two-monic input with H=K², h=2H+1, J=phi(K)=K/3,
root lists y_j and weights w_j=[j]_n, n|K, n>2. For soft-K HH recovery
also choose n>=K^(1/3), with the existing fixed constants. One family has
a unique hit at the nonsplit prime, with the actual factor tag. The
first 5J steps already supply an actual unit-P starting state and a
choice c=0,1,2 with valid adjacent ratios U/(V+cU) and unit increment.

Write f=product_j(1-y_j X), v=sum_j product_(l!=j)(1-y_l X), and
u its w_j-weighted version. The three-state transition matrices commute:
their non-scalar parts multiply to zero. Their exact length-b block
(A_b,B_b,C_b) is acquired by division-free doubling, but its polynomial
degree grows to Jb. The actual initialized execution cost remains

    soft O(J+Jb+h/b),

optimized at b about sqrt(h/J). Commutativity alone does not remove
the cost of acquiring or evaluating the block polynomials.

## 2. A degree theorem for the tag ratio itself

In either good orientation the physical row exponents at the nonsplit
field are Q+c_j P+ell_j, with P<Q, coefficient values separated by 6,
and two opposite phases per coefficient. If

    6P > H*b,

all Jb roots alpha_(j,t)=q^t/y_j of the variable-start block are distinct.
The supplied order bound prevents modular wrapping in this proof.

Hold the acquired starting state fixed, with P_s nonzero, and consider
ONLY its projective tag readout

    R_b(X)=(A_b U_s+C_b P_s)
             /(A_b(V_s+cU_s)+(B_b+cC_b)P_s).

It has no pole at any alpha_(j,t), where its value is exactly
w_j/(1+c*w_j). Thus R_b(qX)-R_b(X) vanishes at J(b-1) distinct points.
It cannot vanish identically: a nonconstant q-invariant rational function
has degree at least ord(q), whereas this block has degree at most Jb,
and its two distinct tag values forbid constancy. Consequently the reduced
numerator/denominator degree d satisfies

    d >= J*(b-1)/2.

This permits every common-factor cancellation and fixes the initial state;
it is stronger than a degree count for the unnormalized product. On a
prepared balanced-size branch P>=c0*K³, length b=eta*K with fixed
0<eta<6c0 gives d=Omega(K²). The older b~sqrt K gives Omega(K^(3/2)).

The theorem is conditional on the stated prepared size branch. It does
not force preparation to continue on a particular infinite family. It
excludes a uniformly bounded-degree dense rational block/interpolant
there, not a fast evaluation at one scalar, a sparse circuit, or other
representations. The proof and exact scope are in
[projective-advance.md](projective-advance.md), with
[independent review](review-projective-degree.md).

## 3. Paid inverses and projectors from the paired families

After separately routing the constant number of a=1 exceptions, all
A/B cross differences can be certified units in soft K, or a factor is
returned. Monic multipoint evaluation acquires all F_B(y_A); a nonunit
is localized once, rather than expanding J² pairs. Every saturated
global equality has the nonzero short beta label

    2*(ell_A-ell_B+a_A-1-(a_B-1)*N).

The N term dominates, making the existing once-only extractor legal.
Guarded fast half-GCD then supplies R_A F_A+R_B F_B=1 and actual CRT
projectors onto the two root lists. Their ordinary geometric-clock sums
are also acquired in soft K from their O(K) coefficients.

This proves that the companion is invertible at the desired family's
roots, without evaluating its whole long norm. It does not make a root
projector into a clock-membership indicator: nonhit clock points still
contribute, and the companion can have zeros at other clock indices.
The missing cofactor weights or a singular solve remain necessary.

Within a good family, all row roots are also distinct: different
coefficients have exponent gap at least 6P-H, and equal coefficients
have two distinct opposite phases. An F' multipoint/discriminant screen
therefore returns a proper factor or certifies global separation in
soft J. It licenses tag interpolation W(y_j)=w_j. The interpolation
and derivative-screen algorithms are old credit; the new arithmetic
guarantee is in [separation-review.md](separation-review.md).

The paired report additionally derives the exact three-adic sibling
identity

    product_(s=0)^2 y_s = y_middle³ * (pi^(H/9))^L,

with an acquired integer |L|<=27. The linear factor dependence cancels,
and H/9 divisibility follows directly from the public phase congruences.
The other two symmetric coefficients remain; this is not a cubic
root-of-unity orbit or a computed clock norm. See
[paired-contraction.md](paired-contraction.md) and its
[review](review-paired-contraction.md).

## 4. Test rational summation with both endpoints paid

For the q-product coefficients, with rho=q^-1 and A=rho^h,

    a_(t+1)/a_t=(A-rho^t)/(1-rho^(t+1)).

The proposed quotient-valued q-Gosper certificate R(z) satisfies

    x*(A-z)*R(rho*z)-(1-rho*z)*R(z)=1-rho*z,

where x is X modulo the acquired row polynomial. If its endpoints are
regular, it would give the long sum from -R(1).

The final 5J original clock steps can also be screened in soft J.
Every global leaf equality in this window has positive short scalar
label ell+a+bN-Hi>N-2H²-H/2, so the factor-return branches are paid.
After both endpoint strips return units, no admissible rational certificate
with numerator and denominator degrees at most 5J can exist for this
ansatz. Finite nonzero poles would require a very long q-orbit arc;
a pole at zero or a polynomial part forces an endpoint resonance that
the actual screens exclude. A denominator specializing identically to
zero is not a valid rational certificate.

The same argument works with any chosen strip width 1<=L<=H: the
screen costs soft(J+L), and excludes certificates of both degrees <=L
on unit continuation. Thus a nearly linear degree allowance can be
matched by nearly linear endpoint screening; the constant 5 is not
essential to this test.

This is a finite-field proof for the explicit summation equation, not
a transfer of a characteristic-zero symbolic theorem or a lower bound
for other scalar contractions. The detailed proof is
[rational-certificate.md](rational-certificate.md), with
[independent review](review-rational-certificate.md).

Coefficient multisection was also executed: stride B shortens each
stream but produces B hypergeometric numerator/denominator parameters
and, in the literal full rational-section construction, JB coefficients.
At B~K this completion costs soft K². A compact joint contraction is
not excluded. The formulas and source contracts are in
[hypergeometric-contraction.md](hypergeometric-contraction.md) and its
[review](review-hypergeometric.md).

## 5. Consequence for the next algorithm

The projective starting states, paired inverses, tag interpolation and
ordinary short clock statistics are paid inputs. Bounded-degree rational
block normalization and the tested small rational q-Gosper certificate
do not provide the long readout. A useful next result must compute the
selected scalar or norm variation without constructing that rational
block, or perform a genuinely joint multisection/paired contraction that
retains the collision contribution. The degree theorem leaves those
possibilities open; another change of homogeneous coordinates is not
itself such an algorithm.

Three Sol 6.1 investigations, independent cross-reviews and a primary-agent
audit are retained. These are paper results, not Lean certificates.
[Sources](sources.json), [review metadata](review.json) and
[file hashes](manifest.json) record scope and preservation. All 961 prior
protected files, two document prefixes and 23 concurrent files are
preserved. No factoring implementation, numerical campaign, Lean/public
assets, commit or push was performed.
