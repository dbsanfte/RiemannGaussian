
## 2026-10-24: quadratic product tests and exact Somos rejection

This pass tests the actual initialized quadratic family against three
candidate fast-product routes. It proves that constant Somos-4/5 cannot
represent any continuing row's cumulative product under the native
guards, including the repeated-spectrum cases. It also acquires the
full antipodal contraction and executes a separable universal block.
None improves the whole-query cost soft(J+sqrt(JL))=soft k^(3/2).
This is evidence for rejecting specific shortcuts, not a sixth-rate
advance or a lower bound on another recurrence or factoring algorithm.

Keep the preceding rank-two constructor, its all-row acquisition and
original norm-leaf consumer. Write w=bar(z), t=z*w=beta^(2H), and

    h_j(n)=Norm(V_j-z^n)
          =c_j+t^n-bar(V_j)z^n-V_j w^n,
    P_j(n)=prod_(0<=i<n) h_j(i).

All targets are units. The beta guards give ord(t)>16k^2 at both primes;
the actual z screen certifies z^d-1 and w^d-1 units for d<=16k^2.
Acquire a fixed number of initial h values per row and handle any
nonunit as an ORIGINAL bounded leaf. This costs soft k. The following
rejections concern the remaining rows and do not assign the old decoder
to auxiliary residuals.

A constant Somos-4 proposal for P gives the cleared residual

    R(n)=h(n)h(n+1)-a h(n)h(n-2)-b h(n-2)h(n-1).

Products of shifted h sequences have an acquired monic scalar
annihilator of order ten, from the pair products of 1,t,z,w. Ten
consecutive zero residuals therefore certify the proposed identity;
fitting a,b uses guarded constant-size elimination, with proper pivot
gcds giving factors. This initially looked like a cheap row filter.
It is vacuous for this source: no continuing row can pass.

The proof uses the unknown nonsplit field only for reasoning. The norm
of z^a w^b is t^(a+b), so spectral values of different total degrees
zero through four cannot coincide. If z!=w, the isolated degree-zero
channel forces b=1-a. The two degree-one channels then force

    a=2+z+z^(-1)=2+w+w^(-1),

contradicting (z-w)(t-1)!=0. If z=w=B0 and Tr(V)!=0, the degree-one
and degree-three channels instead force two a values whose difference
is (B0+1)(B0^4-1)/B0, nonzero by the short guards. If Tr(V)=0, the
two remaining bases 1,t force t^(-1)(t^2-1)(t^3-1)=0, also impossible.
Thus degeneracy of the spectrum does not escape the rejection.

Constant Somos-5 was tested separately. Its residual is
h(m)h(m+1)-a h(m-3)h(m)-b h(m-3)h(m-2). The same channels give
a=1+z+z^(-1)=1+w+w^(-1); in the repeated-spectrum cases the remaining
conditions contradict the short guards through factors B0^6-1 or
t^(-1)(t^3-1)(t^4-1). Fixed unit quadratic gauges of P merely rescale
the constant coefficients, so they do not repair either mapping.
No claim is made about higher-width, variable-coefficient, or different
nonlinear observables.

There is also a direct support reason to be careful with such formulas.
After a first collision, the actual cumulative P is zero forever in
that local field. Substituting this first zero into either constant
Somos identity forces both coefficients to vanish, contradicting an
earlier nonzero left side. This argument uses the product values
directly and does not divide after a zero. An elliptic-net recurrence
cannot be substituted for the cumulative product merely because each
individual h has a common fourth-order LINEAR recurrence.

An actual nodal-curve construction was initialized as another test.
For y^2=x^3+x^2 and phi(v)=(4v/(v-1)^2,4v(v+1)/(v-1)^3), its supplied
division polynomial is

    psi_n(phi(v))=2^(n^2-1) v^[n(n-1)/2]
                    (v^n-1)/(v-1)^(n^2).

The certified denominator makes this a cheap genuine evaluator, but
its support is torsion v^n=1, not v=z^i for a bounded geometric segment.
The z screen expressly excludes z^L=1. Translated endpoints compute
one difference; the finite orbit divisor still needs its shifted right
blocks. The x-only comparison also retains the reciprocal companion.

A formal Tate period Q=Z^L would make Z an L-torsion class, and the exact
theta multiplication identity can be written down. It introduces actual
infinite tails instead of the finite desired product. Moreover there is
no B-algebra specialization of B[[Q]] sending Q to the finite-ring UNIT
z^L: some d has (z^L)^d=1, whereas 1-Q^d is a formal unit. Finite series
truncation does not supply the required curve/point values. This rejects
that initialization route, not every algebraic elliptic representation.

The colour fusion has a positive, fully acquired intermediate result.
Every native a_j has chi_D(a_j)=-1. Antipodal pairs have opposite colours
and give the actual quadratic X^2-S_j X+c_(a,tau), with
c_(a,tau)=beta^[2(N+a)]z^tau and S_j=V_j+V_-j. All S_j and the group
polynomials P_(a,tau)(U)=prod(U-S_j) cost soft k. Their total degree is
J/2. The remaining streams are z^i+c_(a,tau)z^(-i), with varying centers.
Normalizing the acquired square roots of those centers replaces them
by varying starts; inverse tags do not remove those starts. Transport
to the swapped own factor retains an explicit unknown-P carry and only
an O(k^3) bound for its new index, so dropping one colour is unproved.
An all-start overcover has an actual scalar sum decoder with |delta'|<4H,
but its acquired family and query cost soft k^2.

Optionally kill W's 2-part by a public power of two, then RERUN the
actual seed screen for the changed seed. All E_j, Texp_j and H are
divisible by four. Quarter exponents preserve exactly the masks of
this PROJECTED family, since its component groups have odd orders.
The projection itself preserves coverage, not every previous mask.
The quarter seed is likewise actually guarded. J and L do not shrink.

Finally, the universal common-recurrence block is genuinely separable:

    K_b(X,Y)=prod_(i<b)(XY+t^i-X w^i-Y z^i)
            =P_b(X) bar(P_b)(Y),
    P_b(X)=prod_(i<b)(X-z^i).

This avoids a false dense b^2 coefficient cost and evaluates one block
for all J rows in soft(b+J). Its executed whole-interval contraction
still needs J floor(L/b) scaled row states, at cost soft(J+b+JL/b).
Primary amortized-evaluation, accumulating-remainder-tree, and
rectangular-matrix-multiplication theorems were checked with their actual
preprocessing, coefficient, point, field, and genericity hypotheses.
The tested substitutions certify no intermediate saving below k^(3/2).

Reports, primary PDFs, exact independent reviews and the preservation
validator are in `/tmp/semiprime-quadratic-product-20261024`. No examples,
broad Lean build, commit or push were used. The constant-Somos route is
now rejected for this source; the nonautonomous shared contraction is
still unacquired. Preserve all earlier prefixes, 270 frozen entries and
concurrent RH work. The one-sixth goal and full bit/Lean proof stay open.
