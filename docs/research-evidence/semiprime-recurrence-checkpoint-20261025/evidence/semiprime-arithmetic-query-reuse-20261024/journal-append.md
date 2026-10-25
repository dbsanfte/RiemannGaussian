
## A complete signed-weight query at the fixed sixth-root scale, 2026-10-24

This pass obtains a positive whole-attempt improvement: at the actual
scale k=Theta(N^(1/6)), the signed two-weight construction has a complete
deterministic factor-or-query execution costing soft k^(5/4), or
soft N^(5/24), including setup, every public size bin, localization and
factor recovery. The old fixed-scale execution cost soft k^(3/2).
This is a paper algorithm and bit-cost proof, independently reviewed;
it is not a completed Lean implementation or the target sixth-rate proof.
It is also slower than the known global fifth-rate factoring algorithm.

The advance combines the OLD signed two-weight lattice family from the
earlier “Signed two-weight construction” section with the OLD finite
q-product baby/giant evaluator and a direct integer-quadratic consumer.
Neither ingredient nor the known fifth-rate optimization is newly claimed.
The new complete composition works at whichever prime is nonsplit, so
ONE unconditional discriminant suffices for this family. It does not
require the earlier QRH smaller-prime orientation palette.

### Paid symmetric setup

Acquire a negative fundamental D0 with Jacobi(D0,N)=-1 and known
conductor c0=|D0| in soft N^(5/32), using the inherited unconditional
Burgess/Lau–Wu scan and public-small-integer factorization. Its explicit
scan/size failures retain the complete finite-exception fallback; no
numeric threshold is claimed. The [Lau–Wu primary Theorem 1](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf)
applies to nonprincipal characters of cubefree composite modulus, with
strict exponent slack below 5/32. No QRH result is used here.

Set K0=ceil(N^(1/6)); under guard 54c0<=K0 use the least e>=3 with
k=2c0*3^e>=K0, so K0<=k<3K0. FIRST perform the actual small-factor
prefix through 16k^2, or the common bound 16(3K0)^2, in soft k.
The surviving branch has N=PQ<=k^6, distinct odd P,Q>16H, H=k^2,
and therefore k>16. Even inputs, squares and finite guards have their
inherited complete branches. No prefix through sqrt(N/k) is required.

Actually run the scalar and norm-one torus suppliers and rough cleaning
at this k,D0. Both local orders of beta and W are odd, k-rough and >16H,
or a factor is returned, in soft k. These suppliers are symmetric in
the two primes. In B=(Z/N)[tau]/(tau^2-D0), put pi=beta W,
barpi=beta/W and q=pi^H; rerun the actual coupled screen through 16H.
At the nonsplit prime R, which may be the LARGER prime, the two odd
orders divide R-1 and R+1 and are coprime. Thus

    ord_R(pi)=ord_R(beta)*ord_R(W)>256H^2.

Roughness preserves this order under H powering. Any coupled-screen
nonunit has a proper norm gcd, since it cannot vanish in the nonsplit
field. The successful screen provides actual global short units.

### Public weighted rows and guaranteed shorter coverage

Run bins B0<=R<2B0 SEPARATELY for all powers of two B0<=N.
For each unit tag j mod k, put s=[N*j^(-2)]_k and Gauss-reduce

    (k*B0^2,0), (s*B0^2,N).

The resulting nonzero vector is (a*B0^2,b*N), with a*j^2=b*N mod k.
Its squared length is at most (2/sqrt3)*k*B0^2*N. In the correct bin
EVERY resulting row, including signed or zero coefficients, satisfies

    |a|R+|b|(N/R)<4sqrt(kN).

All entries have O(log N) bits even in wrong bins, so exact Gauss
reduction and the O(k) actual rows per bin cost soft k overall.
Acquire D_j=(a*j^2-b*N)/k, t_j=[D_j*j^(-1)]_k and the centered lift

    ell_j=[-2a*j+k*t_j]_H,   -H/2<=ell_j<H/2,
    V_j=pi^ell_j * barpi^(a+b*N).

For f_j(X)=aX^2+ell_j X+bN, both f_j(j)=0 mod H and f'_j(j)=0 mod k;
hence f_j(j+ku)=0 mod H for every integer u. At the own tag j=[R]_k,

    I=(aR+b(N/R)+ell_j)/H is an integer,  V_j=q^I locally at R.

The local exponent identity follows from Frobenius pi^R=barpi and
barpi^N=pi^(N/R), and holds for EVERY row. Frobenius is used in the
proof only; no hidden prime is an algorithmic exponent input.

Take Dceil=ceil(sqrt(kN)), M=ceil(4Dceil/H)+2 and h=2M+1.
The shifted actual targets T_j=q^M V_j have a hit in 0<=t<h, with
original signed index i=t-M. The exact bounds give

    h=O(1+sqrt(N)/k^(3/2))<=8k^(3/2)+7+8/H<16H.

This is full-family arithmetic coverage, with no unique-hit premise.

### Actual product acquisition and a consumer for every saturated leaf

For one bin, acquire prod_j prod_(0<=t<h)(T_j-q^t). With J<=k and
d=min(h,ceil(sqrt(Jh))), build P_d(X)=prod_(u<d)(1-q^u X), and perform
monic MPE at ALL actual giant arguments q^(dg)*T_j^(-1). Acquire and
evaluate the literal residual block too. Arrays, points, values and
products cost soft(d+Jh/d+J)=soft(J+sqrt(Jh)). No point separation or
collision value is inverted. The known unit prefactors recover the
exact product if needed.

A proper norm gcd factors; gcd 1 rejects the bin. A saturated product
is localized by binary row/index restrictions using this SAME evaluator.
Norm multiplicativity guarantees a nonunit child; proper children factor,
otherwise descend a saturated child. Only logarithmically many bounded
subqueries are needed. Multiple hits and fully saturated leaves are legal.

In the correct bin, EVERY selected saturated leaf yields
ord_R(pi) dividing K=aR+b(N/R)+ell_j-H*i, while

    |K|<8sqrt(kN)+(7/2)H+4<3H^2<ord_R(pi).

Therefore K=0 as an INTEGER. The nonzero integer polynomial

    aX^2+(ell_j-H*i)X+bN

has the proper factor R as a root. Use exact discriminant/root tests
when a,b are nonzero. When a=0, use R=bN/(H*i-ell_j); when b=0, use
R=(H*i-ell_j)/a and discard root 0. Test all divisibility and properness
conditions. The pair (a,b) is never (0,0). No positivity, primitiveness,
inverse of a or b, beta-annihilator oracle or deletion of apparent
scalar-trivial rows is required.

SEPARATE bin execution is essential: wrong-bin leaves need not satisfy
the small-integer bound. Each wrong bin may factor or fail boundedly,
then execution continues. The correct bin contains a witness, and ANY
saturated leaf selected within it factors. Aggregating bins before
arbitrary-leaf decoding would lose this guarantee.

### Total bound and the remaining acquisition task

All setup and bin metadata cost soft k. Charging every bin, actual
block, value, residual tail and localization gives

    soft(k+N^(1/4)/k^(1/4))
       =soft(k^(5/4))=soft(N^(5/24)) at k=Theta(N^(1/6)).

The remaining gap for this family is a factor k^(1/4), or N^(1/24),
to the target soft k query. Optimizing the same displayed tradeoff at
k~N^(1/5) recovers the KNOWN fifth exponent. It is not a new global
record. The old constant-triple/hierarchy query has not independently
become faster; this bound is for the newly completed signed-weight route.
The full sixth-rate theorem and its executable Lean bit proof remain open.

A separate audit of [Bacik–Ouaknine–Worrell's bounded Skolem theorem](https://arxiv.org/abs/2507.11234)
actually initializes each old triple as a fixed-order integer recurrence
in soft k total. Its exact-integer-zero candidate theorem does not cover
unknown-prime divisibility. The literal hidden-prime interpolation also
requires more than L residue subsequences. This is a scoped failed
application, not a modular recurrence lower bound, and is not used in
the positive result above.

Exact sources, independent reviews and preservation validation are in
/tmp/semiprime-arithmetic-query-reuse-20261024/. Preserve every prior
prefix, all 270 frozen entries, HEAD and concurrent RH/DeltaNet work.
No numerical coverage campaign, backend lemma batch, commit or push.
