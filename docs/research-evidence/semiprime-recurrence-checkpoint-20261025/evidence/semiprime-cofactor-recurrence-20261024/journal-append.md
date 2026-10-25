
## An initialized three-state recurrence for unique-hit recovery, 2026-10-24

This pass supplies a directly executable scalar contraction, with its true
starting state. It avoids acquiring the full remainder or a large Bezout
matrix. Its proved cost is still soft sqrt(JL)=soft k^(3/2), for J of
soft-k scale and L=3k²+2. Neither the native query exponent nor the separate
known fifth-bound factoring algorithm improves. The one-sixth goal and its
complete executable Lean bit-cost proof remain open.

Sources in `/tmp/semiprime-cofactor-recurrence-20261024`:

- `cofactor-contraction.md`, SHA256 `e4100f7c507a1f3a894b9c9285425b942f086f0080e3f2ef51bd2b0aa7838ee0`.
- `sectioned-convolution.md`, SHA256 `0d091f604177354cf4d9a6fa4e6f709bbff5820b708e3f4c8f0a866a8f211237`.

### Relax the output to two ordinary derivatives

Use the actual prepared canonical minus roots and labels, acquired
F(X)=prod_j(X-V_j), and x_i=q^i, 0<=i<L. Define

    A_n=prod_(r<n)F(x_r),
    T_s,n=sum_(i<n) x_i^s prod_(r<n,r!=i)F(x_r), s=0,1.

The new sufficient outputs are T_0,L and T_1,L, not the exact Bezout
cofactors. If the smaller nonsplit prime has exactly one hit index I,
then locally

    T_0,L=prod_(r!=I)F(x_r) != 0,
    T_1,L=x_I T_0,L.

Thus their ratio identifies the original collision root. The acquired
T_0,L norm gives a proper factor or a unit, never saturation at this
promised field. On the unit branch compute alpha=T_1,L/T_0,L and use
the preceding packet's actual F(alpha) validation, root-product
localization and single original-row locator. This costs soft(J+sqrt L).
Wrong labels use its bounded-failure wrapper; the full fallback is deferred
until all orientation attempts have been tried. The earlier orientation
palette remains explicitly conditional on its QRH import. No global
uniqueness, split-field inference or independent fast cover is assumed.

The prefix state starts at the PUBLIC vector (1,0,0), and its exact step is

    A_next=F(x)A,
    T_0,next=F(x)T_0+A,
    T_1,next=F(x)T_1+xA,       x=q^n.             (1)

This transition is polynomial of degree J (J>=2), with constant dimension
three. It never divides by a hit factor, a state entry or a q-factorial.
It is valid globally through every zero pattern. Equivalently, in the
rank-three algebra with e²=eh=h²=0,

    prod_(i<L)(F(x_i)+e+h x_i)=A_L+e T_0,L+h T_1,L.

The outputs are the first Hasse/ordinary derivatives with respect to the
constant and linear perturbations of F. This explicitly supplies the
starting state that a recurrence evaluator requires; it does not supply
the endpoint at a faster clock.

Choose a dyadic block length b~sqrt(L/J). Build the actual polynomial
matrix product M_b(X)=M(q^(b-1)X)...M(X) in soft Jb work, evaluate it at
the actual floor(L/b) giant starts q^(bg), and multiply the resulting
constant-size matrices. Acquire and process the clipped tail as well.
Monic MPE and fixed-rank arithmetic over the actual quadratic algebra are
lawful without singular inverses. All starts, arrays, products and the
consumer are paid: soft(Jb+L/b+J+sqrt L), hence soft k^(3/2).

Constant state dimension does not remove the polynomial degree. The
off-diagonal block entries are

    U_0,b(X)=sum_(t<b)prod_(r<b,r!=t)F(q^r X),
    U_1,b(X)=X sum_(t<b)q^t prod_(r<b,r!=t)F(q^r X).

Their top coefficients are q^[Jb(b-1)/2] times sum q^(-Jt) and
sum q^((1-J)t), respectively. For dyadic b, each sum factors into
1+odd-order-group-element factors, all units in every actual component.
Their degrees are therefore EXACTLY J(b-1) and J(b-1)+1. This tests the
literal commuting/triangular block representation, not every possible
implicit block action or scalar contraction.

### Exact cofactors are also acquired at the retained clock

For G_L(X)=prod_(i<L)(X-x_i), let lambda_i=1/G_L'(x_i). The exact
complementary-grid identity for the previously defined Bezout matrix is

    adj(K)_(0,s)=(-1)^[J(J-1)/2+JL+1]
          *sum_(i<L) x_i^s lambda_i prod_(r!=i)F(x_r), s=0,1.

Prove it first by partial fractions at independent formal roots, then
clear the certified unit discriminants. No F(x_i) is inverted. This
stronger output is distinct from (1)'s sufficient derivative sums.

Here lambda_0=(q;q)_(L-1)^(-1) is actually acquired in soft sqrt L, and
lambda_(i+1)/lambda_i=rho(x_i), where

    rho(X)=q(1-q^(1-L)X)/(1-qX).

The weighted state (Z,B_0,B_1) starts at (lambda_0,0,0) and updates as
(rho F Z, F B_0+Z, F B_1+XZ). Set lambda_L=0 for the last update.
Clearing the known unit 1-qX gives a degree-(J+1) polynomial matrix;
the total denominator (q;q)_L is actually acquired and inverted. The
same block execution acquires both exact cofactors at soft sqrt(JL).
The vanishing terminal Z is not an unknown initial amplitude.

The weighted normalized B_0 block contribution W_b, after clearing only
(qX;q)_(b-1), has full degree (J+1)(b-1), with unit leading coefficient proportional to
sum_(t<b) q^[t(1-L-J)]. Removing the shared F block would erase the
detector on the block containing the unique hit. A tested q-Gosper
certificate lambda_i r(x_i)/F(x_i) has no polynomial r of degree
<=L+J-2; degree L+J-1 is resonant and is NOT excluded by the leading
coefficient argument. On the optional branch where F(1),F(q^L) are
actually certified units, a unique interior pole excludes this particular
polynomial-numerator certificate at every degree. A nonunit outside
endpoint is not silently sent to the original interval decoder. These
are scoped certificate checks, not recurrence lower bounds.

### Check the new polynomial-reduction paper on this instance

The primary [Wang--Yang--Zhong 2026 paper](https://arxiv.org/abs/2606.07061)
works over characteristic-zero K(q), with q indeterminate. Its adjoint
summation and Laurent-polynomial degree reduction do not state a fast
finite-endpoint or composite-ring specialization theorem. For the formal
sequence a_n=1/F(q^n), the actual annihilator and adjoint are

    L=F(qX) sigma-F(X),
    L* p=F(X)(p(X/q)-p(X)).

Every Laurent-polynomial certificate weight in that image is divisible
by F. With J>1 and F(0) a unit, neither requested weight 1 nor X lies
there. Exponent zero is also an explicit extreme-degree resonance.
The analogous weighted adjoint again has factor F. These identities
are checked from acquired coefficients; they neither evaluate the residual
sums nor exclude rational certificates with additional poles.

The sectioned-convolution interface remains specific: with A the long
q-Pochhammer numerator, D=prod_j(1-V_jT), C=A/D satisfies
(1-T)D(qT)C(qT)=(1-q^LT)D(T)C(T). Its short initial prefix is acquired,
but a far coefficient still requires the particular paired contraction
of truncated q-binomial sums. The existing fast reshape matvec does not
supply that row-dependent contraction. No rate improvement is inferred
from the short operator or from formal power-series composition.

The constructive advance is the initialized, division-free sufficient
three-state query and its fully paid exact-cofactor variant. The next
algorithmic target is to apply its implicit blocks faster than expanding
degree Jb, with every start, specialization and original label preserved.
All earlier prefixes, all270 frozen entries and concurrent RH work remain.
