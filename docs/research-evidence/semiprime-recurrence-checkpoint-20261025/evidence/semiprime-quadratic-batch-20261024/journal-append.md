
## Reciprocal recurrence boundaries and the filtered theta attempt, 2026-10-24

The preceding turn supplied a reviewed canonical quadratic row family;
the acquisition exponent remained unchanged. This pass executes three
attempts to use it: recursive reciprocal folding, a finite-theta product,
and a self-dual low-curvature enlargement. Both coefficient boundaries
of the reciprocal-grid polynomial are now acquired at the intended small
clock. Its terminal remainder is still missing. The complete covered query
remains soft(J+sqrt(JL))=soft k^(3/2), not soft k. No one-sixth factoring
or full executable/Lean bit-complexity theorem is claimed.

### Actual reciprocal initialization and the remaining operation

For the original even L=2n, put a=q^(1-L) and
c_L=q^(L(L-1)/2). Direct reversal gives

    P_L(y)=c_L*y^L*P_L(a/y), P_L(y)=prod_(i<L)(1-q^i*y).

Acquire the reciprocal points a/y_j and
A(Z)=prod_j(Z-y_j-a/y_j). The algebra
B[Z,T]/(A(Z),T^2-ZT+a) is free of rank two over B[Z]/A even when new
point differences are nonunits. Its involution T->Z-T=a/T needs no new
separation hypothesis. Pairing factors gives

    P_L(T)=c_L*T^n*prod_(i<n)(Z-q^(-i)-a*q^i).

The constant Dickson fold is credited to earlier work. For an actual
half-product h0(Z)+T*h1(Z), the relative norm is
h0^2+Z*h0*h1+a*h1^2, including at zero values. These formulas provide a
lawful merge, but acquiring h0,h1 still requires the midpoint data.

The next involution changes: r_m r_(2m)(y)=q^m*y. At a depth with L=mG,
the actual starts are q^(mg)*y_j, 0<=g<G. Shared evaluation of ONE baby
polynomial P_m costs soft(m+JG+J), optimized at the existing sqrt(JL)
scale. Clipped tails retain their actual intervals.

There is a stronger cheap initialization. Let F(T)=prod_j(T-y_j) and
R_G(T)=prod_(j,g<G)(T-q^(mg)*y_j), of degree JG. Then exactly

    F(q^(-m(G-1))*T)*R_G(q^m*T)=F(q^m*T)*R_G(T).

Its degree-J generators cost soft J. If p_r=sum_j y_j^r, the grid power
sum is p_r*S_G(q^(mr)), where S_G(X)=1+X+...+X^(G-1). Compute the first
m native power sums from F, then evaluate the ACTUAL polynomial S_G by
monic multipoint evaluation. Newton logarithm/exponential acquires the
top m monic coefficients of R_G in soft(J+m+G). Only integers through m
are divided by, all units here. In particular this does not assume that
1-q^(mr) is invertible when mr exceeds the short seed guard.

For the acquired reciprocal augmentation, the grid root centre is
a*q^(m(G-1))=q^(1-m). The constant coefficient and normalization are known
units, so its bottom m coefficients follow from the top ones at the same
cost. Thus both boundary vectors and the recurrence generators are actual
data when mG is exactly the reciprocal product length.

The balanced native instance uses the MAIN prefix L0=2H, with m=k and
G=2k, and rebuilds its reciprocal augmentation using a0=q^(1-L0).
The final TWO original factors, at q^(2H)*y_j and q^(2H+1)*y_j, are acquired
in soft J and keep their actual tail indices. The main two-boundary data
therefore really cost soft(J+sqrt L), without assuming that 2H+2 admits
balanced divisors. For the repaired horizon 3H+2, the same construction
uses L0=3H, m=k, G=3k and again a two-factor tail.

The unresolved operation is R_G mod P_m, or the equivalent terminal
resultant, using those data without the full middle coefficient vector.
For an exact-length augmented grid the resultant is a known unit times
the square of that product. In the balanced native implementation it is
the MAIN-prefix product squared; multiply by the acquired tail product
squared for the full query. Main reciprocal leaves map back to the
original row and reversed index L0-1-i; tail and interval restrictions
keep their separate actual index maps.
Folding both reciprocal polynomials again only gives the already known
constant degree reduction. No approximant-basis solver or terminal value
is assumed merely from having two boundary vectors.

There is a uniform GLOBAL distinctness check for the ORIGINAL grid.
For m>=6, equality q^(mg)*y_j=q^(mh)*y_h implies that the odd global beta
order divides delta_j-delta_h-Hm(g-h). Its magnitude is less than
5H+4H^2, below that order (>256H^2). Hence it is zero as an integer;
the delta span<5H forces g=h, and global target dedup forces j=h.
The JG original points are therefore distinct on every prepared input.
Materializing that whole grid really has JG outputs; together with an
explicit degree-m baby polynomial, this output-task cost is at least
m+JL/m. This is a statement about full explicit materialization, not a
lower bound for an implicit solver or a factoring execution that stops
early upon finding a factor. Local unit separation is not inferred from
global distinctness, and augmented cross-pair distinctness is not assumed.

### Finite theta pairing retains its varying centres

For the repaired family in the rest of this entry, take L=3H+2. Negation
preserves [Nu^2]_H<2k and flips the
negative fundamental character. The actual antipodal row products are

    V_+*V_-=beta^(2(N+a'))*q^mu, mu in{-8,...,0}.

Writing x=1/V_+ and z=1/(V_+V_-), the correct pair is
Psi_L(x,z)=(x;q)_L*(z/x;q)_L. The finite theta special case z=q satisfies

    Theta_L(x)=(-1)^L*x^(-L)*q^(L(L+1)/2)*P_(2L)(x*q^(-L)),
    Theta_L(x)=sum_(t=-L)^L (-1)^t*q^(t(t-1)/2)
                              *[2L choose L+t]_q*x^t.

These are finite Laurent-polynomial identities; their required q guards
through 2L are paid. The general centre has the exact boundary equation

    (1-x)*(1-z*q^(L-1)/x)*Psi_L(q*x,z)
          =(1-q^L*x)*(1-z/(q*x))*Psi_L(x,z).

It holds through zeros. It is not a license to divide a zero boundary.
Even the theta case retains finite endpoint factors instead of pure
monomial quasiperiodicity. The primary infinite-theta determinant and
finite Ramanujan identities were inspected with their actual hypotheses;
neither supplies the missing filtered-product evaluator.

There are Theta(k) actual centre classes: each a' supports at most sixteen
tags, while equality of two centres forces
4(a'-a'')+2H(mu-mu')=0 by the large GLOBAL beta-order bound, and thus both
labels agree. There is also a stronger uniform alignment result: NO
actual centre can have z=q globally. If C*q=1, pass to the unique nonsplit
side. The odd scalar beta order divides r-1 and the odd W order divides
r+1, so they are coprime. Thus W^(H(mu+1))=1; its order>16H and the
exponent magnitude<=7H force mu=-1. Global equality now forces the odd
global beta order to divide N+a'. Since it also divides (P-1)(Q-1),
it would divide the positive integer P+Q+a'-1<H^2, contradicting its
lower bound256H^2. This uses coprimality at the nonsplit side, not an
unsupported coprimality at the split side.

The acquired centre tests therefore return a proper factor or a unit;
their globalzero branch is impossible. There is no guarantee that these
tests find a factor, but on continuation the special finite-theta centre
never occurs. The complete varying-centre algorithm still pays all mixed starts and
costs soft(k+s+kL/s), optimized at soft k^(3/2). Its restricted products
and all theta-factor index maps retain original repaired leaf consumers.
Neither the centre count nor this specific alignment obstruction precludes
a new algorithm coupling varying centres.

### A self-dual enlargement is valid, but retains the hard strip

For the full acquired filter Fset={u in U(H):[Nu^2]_H<2k}, reflection
R(u)=1-u interchanges a(u)=[Nu^2]_H and e(u)=[N(u-1)^2]_H. Every u is
odd, so R(u) is NEVER a native unit tag. Nevertheless R(Fset) is an
actually acquired disjoint set, and Fset union R(Fset) has 4phi(k)=O(k)
points. For a fixed bounded carry eta, with K=q^(floor(N/H)+eta), define

    A_eta(X)=prod_(u in Fset)(X-K*pi^e(u)),
    B_eta(X)=prod_(u in Fset)(X-K*pi^a(u)).

Both polynomials are acquired in soft k. On the reflected strip the two
products swap. Thus the self-dual product is A_eta*B_eta in either
description; reindexing retains A_eta rather than evaluating it.

There is a fully lawful covered enlargement: include both strips for all
seven eta values and retain the original minus-colour rows. Every new
plus-type exponent E has -6H<E-N<2H. At a saturated new norm leaf, the
nonsplit side gives the scalar beta witness; its saturation forces
|(1+Hi-(E-N))-(P+Q)|<4H^2 below the global beta order. Hence the actual
factor sum is recovered. All extra leaves have a proved consumer.
For distinct extra pi-power targets, the exponent gap d has |d|<8H<C;
pi^d-1 divides the certified unit q^d-1. This proves unit separation even
on split coordinates. Different norms alone would not prove that claim.

The low-a strip still has Theta(k) distinct curvature values: the unit
square map has equal fibres of size at most sixteen. Acquiring its
polynomial does not certify its long interval product is a unit. Computing
that certificate or a consumable nonunit currently costs soft k^(3/2);
if it is a unit, cancellation still leaves the A_eta query. Literal closure
under BOTH reflections u->-u and u->1-u also contains translation by one,
so any nonempty fully closed set has all H labels. This is an explicit
closure count, not a restriction on implicit representations.

The reports and independent exact-source reviews are retained in
/tmp/semiprime-quadratic-batch-20261024. Old reciprocal/Dickson and
antipodal identities are credited. The new paid two-boundary data give a
more specific initialized recurrence problem; its terminal contraction
remains open. All prior shared prefixes, all270 frozen entries and
concurrent RH work are preserved. No example campaign or extra backend
lemma is used as evidence of a faster whole-query bound.
