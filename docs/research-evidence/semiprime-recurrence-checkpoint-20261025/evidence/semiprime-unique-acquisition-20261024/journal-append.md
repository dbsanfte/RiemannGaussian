
## Unique-hit acquisition: a conditional orientation cover and two-coefficient target, 2026-10-24

The complete native query still costs soft k^(3/2), with k at sixth-root
scale; the separate known fifth-bound algorithm and the open one-sixth/full
executable Lean bit-complexity goal are unchanged. This pass supplies a more
specific acquisition target: an actual linear subresultant, or two fixed
Bezout cofactors, suffices for soft-k recovery when the smaller prime is
nonsplit. A conditional polylogarithmic orientation palette supplies that
promise on at least one unrecognized label. Neither result acquires those
coefficients. The executed parity recurrence acquires its first numerator
window cheaply, but its later dense filters grow.

Exact sources and independent reviews are in
`/tmp/semiprime-unique-acquisition-20261024`. Final source hashes:

- `unique-gcd.md`: `8eba0f3676ef0de414f4b48fa463a54058aed4fed97db3a0557be0189ec8c862`.
- `orientation-palette.md`: `97db9cf0004dac3ec2c6c9cc341b27531fb90c51d5f6739e6b121c6bc4e20fbf`.
- `palette-acquisition.md`: `85009ef8ac37c32cc1eef60aed0796c2a150ab756bc30c7c22d7fb2dc6c8159f`.
- `auxiliary-powers.md`: `3aeb1f40b72340face8154ac40657003fdea4078f5ca9cc766868767d4cd6be2`.

### An acquired linear subresultant is enough

Prepare the actual canonical parity-repaired MINUS roots V_j, their retained
labels, and factor-or-unit separation. Let F(X)=prod_j(X-V_j), degree J of
soft-k scale, and G_L(X)=prod_(i<L)(X-q^i), L=3H+2. All these inputs except
the long G_L coefficient vector are acquired. On the smaller-nonsplit branch,
the previous exact-one theorem gives degree gcd(F,G_L)=1 in the local field.

If S_1(G_L,F)=c_1 X+c_0 is actually supplied, c_1 is nonzero at that field.
Consequently gcd(N,Norm(c_1)) is a unit or a proper factor, never N. If unit,
acquire alpha=-c_0/c_1. Evaluate F(alpha) in soft J work. Its norm either
factors N or is saturated; in the latter case the actual coordinate
classifier factors or proves global F(alpha)=0. Localize the supplied
product prod_j(alpha-V_j) in soft J work. At a saturated leaf use that same
classifier to factor or prove global alpha=V_j. This identifies an actual
original row whose P-side root is the unique collision. Its single length-L
query costs soft sqrt L=soft k and uses the original index/leaf consumer.
No split-coordinate equality is promoted to global equality without testing.

Equivalently put h=G_L mod F and define K by

    sum_(r,s<J) K_(r,s) X^r Y^s
      = [F(X)h(Y)-F(Y)h(X)]/(X-Y).

For the actual invertible Vandermonde V, V K V^t is
diag(F'(V_j)h(V_j)). At the promised side K has corank one, with kernel
v=(1,alpha,...,alpha^(J-1)); adj(K)=c vv^t, c nonzero. Thus the two scalars
C_0=adj(K)_(0,0), C_1=adj(K)_(0,1) give alpha=C_1/C_0 and the same consumer.
This is a scalar acquisition target, not a supplied black-box matrix.
In fact the single action K e_0 would already acquire the full remainder:

    h(0)=K_(J-1,0),
    h(X)=[F(X)K_(J-1,0)-X K(X,0)]/F(0).

F(0) is a supplied unit. The cheap reshaped q-binomial action from earlier
work has not supplied this column. The initialized baseline acquires h by
the old blocked evaluations and interpolation in soft k^(3/2), then guarded
subresultant arithmetic costs soft J. There is no new whole-query bound.

For palette composition one can use a bounded FAILURE version of the
consumer: classify c_1, and return failure on global zero; return failure
when F(alpha) is a unit or the identified row's interval is a unit. Proper
gcds are checked factors; saturated tests use the coordinate classifier.
All validations, localization and at most one row query cost soft k on
EVERY label. This is just the source's guarded consumer with its expensive
full-family fallback deferred until all labels have been tried. It does not
make acquisition itself bounded: a future acquisition routine must have an
explicit bounded attempt on every label, and supply the correct ratio on at
least the promised label. Final full-query fallback preserves total
correctness but cannot be charged soft k when invoked infinitely often.

### Execute numerator decimation without assuming initialization

Reverse A(T)=T^L G_L(1/T)=prod_(i<L)(1-q^i T) and
D(T)=T^J F(1/T)=prod_j(1-V_j T). Bostan--Mori's primary
[Algorithm 1 and Theorem 1](https://mathexp.eu/bostan/publications/BoMo21.pdf)
give a nearlinear-order, logarithmic-index clock from an actual supplied
proper numerator. Here A has degree L. The parity identity is still exact,
but that theorem does not supply its reduction modulo D for free.

Write A=A_e(U)+T A_o(U), D=D_e(U)+T D_o(U), U=T². The actual parity step is

    D_1=D_e²-U D_o²=prod_j(1-V_j² U),
    N_e=A_e D_e-U A_o D_o,  N_o=A_o D_e-A_e D_o.

Acquire D_1 from the actual squared roots in soft J. A width-O(J) far
window of either numerator requires only a contiguous O(J) band of A;
the pinned selected-q-coefficient primitive acquires that band in
soft(sqrt L+J). Actual convolution and parity extraction then acquire the
first requested numerator window at soft k, including its initialization.

At stride B=2^s and residue r=n mod B, however, the exact numerator is

    A_B(U)=Section_r[A(T) K_B(T)],
    D_B(U)=prod_j(1-V_j^B U),
    K_B(T)=D_B(T^B)/D(T)=prod_j sum_(a<B)(V_j T)^a.

K_B is a polynomial of degree J(B-1), with unit top and constant1. A
width-w window, w=O(J), needs an A band of width at most
B(w-1)+J(B-1)+1. The executed dense filter/convolution therefore costs
soft(sqrt L+JB), reaching soft L at B~L/J. This is an implementation ledger,
not a lower bound on implicit sectioned convolution or scalar acquisition.
A fixed-width window does not initialize the next one: its backward
dependency needs about twice the width plus J.

The tempting norm A(T)A(-T)=A_(q²,L)(T²) has degree L in U, not L/2,
and supplies A_e²-U A_o² rather than either cross numerator. Odd local
orders do make A(-1/V_j) a unit, so squaring seed and targets preserves
collision support at the same index. It does not shorten the horizon.
The desired two cofactors are not identified with two arbitrary far
coefficients of A/D; that reduction has not been established.

### Conditional orientation supply at the same scale

This paragraph explicitly IMPORTS the pinned QRH Corollary 1.2 consequence
n(p)<=C(log p)^32; it is not a newly verified unconditional theorem here.
Use r=ceil(N^(1/6)), B=bit_length(2N)^33. Under that import, all sufficiently
large N have a quadratic nonresidue <=B for each prime <=N.

First screen every positive integer through M=400r² in soft r by monic
integer blocking, with finite fallback if M>=N. Every leaf is positive<N,
so a nonunit localizes to a proper factor. Otherwise BOTH primes exceed
400r², simultaneously certifying the threshold for all later k_D<5r.

Acquire a small negative fundamental D0 of Jacobi symbol -1: use -4 if
N=3 mod4; otherwise the already pinned Burgess/Lau--Wu scan through
ceil(N^(5/32)) supplies a unit Jacobi-minus integer. Factor that PUBLIC
integer at cost at most soft N^(5/64), select a Jacobi-minus prime ell,
and use -ell, -4ell or -8 according to ell mod4. Its conductor
c0<=4 ceil(N^(5/32)) has only one possible odd prime factor.

Enumerate all positive uv with 1<=u,v<=B, keeping unit Jacobi-plus
products and D0 itself. Small nonresidues for P and Q either already give
one pair of signs (-1,-1), or their opposite sign pairs multiply to it.
Thus one retained uv flips BOTH local signs of D0. Normalize D0uv to a
negative fundamental discriminant D using the known factors of D0 and a
public sieve through B. Square removal and factors4 preserve the signs.
At least one unrecognized D makes the SMALLER P nonsplit and Q split.

Every conductor c<=4c0B²=o(r). Under public guards c<=r/16 and
T_c=max(3,ceil(r/(2c)))>B, sieve primes in two consecutive Bertrand
intervals, select qpub not dividing c, and set k_D=2c qpub. Only ell can
exclude one of the two candidates; all other conductor primes are <=B.
Then r<=k_D<5r and c divides k_D/2. The increased number of conductor
primes means the old literal square-fiber constant16 is NOT retained:
use the proved polylogarithmic bound <=16B² and polylogarithmic content
types. Necessary target preparation still costs soft k_D.

For EVERY label rebuild the actual rough scalar and torus bases, native
character/parity rows and q, and rerun the coupled seed screen. Old bases,
split-side order certificates and points do not transfer automatically.
There are polylogarithmically many labels; all preparation is soft r.
For the good label the earlier bounded-integer and valuation proof gives
exactly one canonical MINUS collision at the smaller nonsplit prime.
It gives no global uniqueness and no such count at the split prime.

The analytic finite exceptions need not be recognized by the public guards.
The whole controller uses a final complete fallback if all bounded attempts
fail. Conditional on the import AND a future successful bounded acquisition
routine, that fallback would be confined to finitely many inputs. Currently
no such acquisition routine is supplied. This pass proves the conditional
promise cover and the consumer separately, not a one-sixth algorithm.

### Two other acquisition proposals, fully charged

Signed two-weight construction: the rank-two lattice
a j²=cN mod k has determinant k. Set ell0=-aj-cNj^-1 mod H; then
HI0=aP+cQ+ell0 at the own tag. For F(P)=aP+cN/P, the scaled derivative
coordinates at a public centre P0, radius Delta, have lattice covolume
kN Delta³/P0³. Fixed-rank LLL gives coordinate bound
T<=2 sqrt(kN)(Delta/P0)^(3/2), and the EXACT remainder gives variation<=3T.
Rational floor centering acquires h=O(1+sqrt(N)eta^(3/2)/k^(3/2))
indices with J=O(k/eta) rows, eta=Delta/S, across all public bins/tags.
Pretest the nonzero linear equation aX-cN for proper divisors BEFORE
removing rows with public integer-zero leaves E=Hz. Remaining global
leaves have nonzero short annihilators and use the general extractor.
Actual full polynomial/MPE and recovery cost soft(J+h+k).
Forcing constant h sets eta~k/N^(1/3) and acquires J~N^(1/3)=k² rows;
balancing recovers the known N^(1/5) construction. Neither is new progress
towards soft k. Demanding universal quadratic vanishing modulo k³ forces
only (k/2)|a, k|ell and (k/2)|c because k is EVEN; dividing that common
content leaves denominator 2k², not an extra k-digit. No generic lattice
or selected-root impossibility follows.

The auxiliary-power/Cheon audit is explicit old-route credit. With known
prime order p, d|(p-1), a supplied primitive scalar generator and actually
acquired g=beta^(H^d), A_(j,1)=beta^[E_j H^(d-1)] and
A_(j,d)=beta^(E_j^d), the shared deterministic two-stage searches
cost soft(sqrt(Jp/d)+sqrt(Jd)+J). Literal acquisition adds soft Jd;
for p~k³ the balance d~k^(2/3) gives k^(5/3), worse than old k^(3/2).
The shared lower-power input A_(j,1) costs soft J, already included.
Free-auxiliary estimates do not pay the high-power input, and roughness does not
supply divisors of p-1. This is not a lower bound on shared acquisition.
An EXACT local beta order r, whichever prime supplied it, already gives
a proper gcd from beta^r-1 or a nonzero global short annihilator and the
existing general extractor. Only the smaller covered side additionally
has the covered index [E H^-1]_r. No larger-side index coverage or
polylogarithmic-bit allowance for wide high-degree exponents is inferred.

The next constructive target is an initialized scalar cofactor contraction
or a compact sectioned-convolution action with a proved whole-attempt cost.
No backend lemma, finite example campaign, certificate count or implicit
matrix descriptor is being counted as acquisition progress. All old
prefixes, all270 frozen evidence entries and concurrent RH work are retained.
