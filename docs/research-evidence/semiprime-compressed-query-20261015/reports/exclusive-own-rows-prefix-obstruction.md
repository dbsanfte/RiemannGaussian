# Exclusive own rows forbid conversion to one common coefficient prefix stream

2026-10-15. New actual-source arithmetic count and an exact representation
obstruction. No fast factoring algorithm, new Lean theorem or general
scalar-query lower bound is claimed.

## Inherited supply and the new statement

Use the SAME original order-qualified balanced ordered prime-pair supply
N=P Q, P,Q=Theta(M^3), P/Q in [2/3,3/2], of mass
Omega(M^6/log^2 M). At every first-K candidate auxiliary prime m=Theta(M),
K_*=O(M^.020), gamma has exact prime local orders R_P>P^.677 and
R_Q>Q^.677, eventually exceeding 16m^2. The original supply has
P,P-1,Q,Q-1 units modulo m^2. Its candidate-selector envelope is

    (m-G_m)^6<N<=m^6,
    sum_m(G_m+1)=O(K_*M),  G_m=o(m).

The frozen observation deletions already permit requiring distinct tags
P mod m != Q mod m simultaneously at every candidate, with loss
O(K_*M^5). That condition is used below only on the qualified pairs to
which the new count applies. The new count can be performed on the
original qualified supply with the distinct-tag condition imposed; its
complement is already charged in the frozen loss.

For completeness that same-tag charge is elementary: at fixed Q,m the
partner selector strip has length O(M^2 G_m), so P=Q mod m permits
O(M(G_m+1)) integer partners. Summing O(M^3) values of Q and the
selector telescope gives O(K_*M^5). No prime distribution in a residue
class is assumed.

Put d=m^2, q=gamma^d, J=m-1. The literal first-current data are

    a_j=N j^(-2) mod m,  1<=a_j<m,
    I_j=j^(-1) mod m,
    D_j=(N-a_j j^2)/m,
    b_j=centered(m,-I_j D_j),
    ell_j=m b_j-2a_j j,
    delta_j=a_j+ell_j in [-3d,d],
    z_j=gamma^(-N-delta_j),
    A_j(L)=P_L(z_j;q)=prod_(i=0)^(L-1)(1-z_j q^i).

For large enough M, after a further deletion of at most

    O(K_*M^5.969)=O(M^5.989)                            (1)

inputs, EVERY candidate m has BOTH exclusive own rows

    gcd(N,A_(P mod m)(L))=P,
    gcd(N,A_(Q mod m)(L))=Q                            (2)

simultaneously for every integer 2m^2+2<=L<=4m^2.
The two tags are distinct. This same family works for ALL common
prefix streams and ALL row-index assignments in the obstruction below;
it is not selected after choosing a proposed coefficient representation.

Union (1) with the frozen soft O(M^5.994) losses and the subsequent
already recorded losses preserves Omega(M^6/log^2 M) actual inputs.
This is an input-exception count, NOT acquisition time. Neither hidden
factor, local order nor own tag is supplied to an algorithm.

## Both own collisions lie inside the native full window

Fix j=P mod m. The actual lift gives

    N=a_j j^2-j m b_j+m^2 c_j

for an integer c_j. Writing P=j+m x, the identity

    P(a_j P+Q+ell_j)=m^2(a_j x^2+b_j x+c_j)

and invertibility of P modulo m^2 show that

    i_P=(a_j P+Q+ell_j)/m^2

is an integer. Its original residual exponent satisfies

    N+delta_j-m^2 i_P=(P-1)(Q-a_j).                   (3)

Thus the P-field residual vanishes at i_P. This is the existing own-seed
coverage arithmetic, applied without changing the actual full-input lift.

The original offset bound gives ell_j>=-3m^2-m and ell_j<=m^2.
As P,Q=Theta(m^3), the numerator a_jP+Q+ell_j is positive eventually.
Balance and N<=m^6 imply

    max(P,Q)<=sqrt(3/2)*sqrt(N)<=sqrt(3/2)*m^3.

Since a_j<=m-1,

    i_P <= [m*max(P,Q)+m^2]/m^2
         <=sqrt(3/2)*m^2+1 <2m^2+2.

The same argument with P,Q swapped proves the Q-own collision in the
same window, including for the larger factor. This is where the fixed
balanced-bin hypothesis matters. It is not asserted for arbitrary
factor ratios merely by swapping the general smaller-factor theorem.

## Delete cross-field hits by counting at most two tags per multiplier

We count inputs where the P-own tag j=P mod m ALSO hits in the Q field
at ANY index 0<=i<4m^2. Fix an admissible local prime Q, m and its
actual R=R_Q. Split its partner-P selector strip into O(G_m+1)
half-open boxes of width at most d. Fix one such box.

Since Q=1 mod R, a Q-field hit is equivalent to

    P+delta_j-d i=k R.                                (4)

Across the complete box, all original indices and all source offsets,
the left side has interval length O(m^4). Hence its possible multipliers
k lie in a common interval of size

    O(m^4/R+1)=O(M^1.969).                             (5)

The own tag constraint j=P mod m forces

    a_j=Q j^(-1) mod m.

Reducing (4) modulo m and using the actual low digit
delta_j=a_j(1-2j) mod m gives

    j+Q j^(-1)-2Q=kR mod m,
    j^2-(2Q+kR)j+Q=0 mod m.                          (6)

This is a MONIC quadratic, independently of k. There are at most TWO
possible j values for each fixed k. No exceptional leading-coefficient
case creates an extra m-sized tag family. Its constant term Q is a
unit, so every root is a nonzero tag. Each fixes one canonical slope a_j.

For two qualifying partners P,P' in that same box with fixed j,a_j,k,
their full lifts give

    m(b_j(P)-b_j(P'))=-I_j Q(P-P') mod m^2.

Subtract (4) modulo m^2. The possibly different i values disappear,
leaving

    (1-I_j Q)(P-P')=0 mod m^2.                       (7)

Distinct own tags give j!=Q mod m; therefore 1-I_jQ is a unit. Hence
P=P' mod m^2 and the half-open box contains at most ONE partner for
this j,k. Equation (4) then determines i uniquely. There is no further
tag, slope, index or cofactor multiplicity.

Equations (5)-(7) bound the cross hits by O(M^1.969) per box. There
are O(M^3) integer Q candidates, and summing the selector boxes gives

    O(M^3 M^1.969 sum_m(G_m+1))=O(K_*M^5.969).

On the qualified supply, R_Q is the intrinsic unique large prime factor
of Q-1 and is fixed after fixing Q; no extra sum over R or v_Q is paid.
Reversing orientations costs a factor two. Delete these inputs on the
same original qualified supply, together with the charged same-tag
exception. Both own rows retain their forced own-field hit and lose
every cross-field hit through 4m^2. Since N is squarefree, (2) follows.

The preceding full-row incidence theorem allowed all m tags per fixed
multiplier. Constraint j=P mod m makes the new quadratic monic and cuts
that factor from m to two. The previous target-pair/root-support and
ordinary row-density counts alone do not imply exclusivity (2).

## One common prefix stream has a chain of prime-divisibility supports

Let V_k be ANY common forward stream over Z/N of the form

    V_k=C_0 prod_(r<k) U_r / prod_(r<k) W_r,  k>=0,   (8)

at the selected indices, where every selected denominator product is
a unit. All quantities may depend on the full N, arbitrary advice,
or the hidden factors; no acquisition hypothesis is needed for this
representation obstruction.

If k<=l and a prime P dividing N divides V_k, then P divides V_l:
the numerator at l is a multiple of the numerator at k, while both
selected denominators are units. Thus the prime-divisibility supports
of the stream form one inclusion chain as k increases. Multiplication
by any row-specific UNIT does not change these supports.

It follows that NO two selected stream values can have gcds P and Q
respectively. If their indices obey k_P<=k_Q, divisibility by P would
propagate to the supposedly Q-only value. The reverse ordering yields
the symmetric contradiction. Equality of indices cannot help.

Consequently the exclusive row family (2) admits NO representation

    A_j(L)=unit_j * V_(k_j)                           (9)

for all original rows through ONE such stream, for ANY index assignment.
The conclusion permits full-N-dependent, adaptive and even private
advised choices. The SAME arithmetic counterfamily defeats every such
single-stream conversion; no union over these choices is necessary.

## Application to a huge common top parameter

For any one common base eta, common nonnegative integer top T and nonnegative
coefficient index k in its valid range, the Gaussian coefficient stream
of P_T(X;eta) has the prefix-ratio formula

    c_k(T)=prod_(r<k)(eta^T-eta^r)
            / prod_(r<k)(1-eta^(r+1)).                (10)

Whenever its selected denominator products are units, it is exactly
of form (8). T, eta and the indices can be arbitrarily input-dependent
or huge; a large top can be powered succinctly. No horizon-inflation
claim is used. Nevertheless (9) cannot hold for every original row.

This closes the huge-COMMON-top escape from the simpler observation
that the original c_0,...,c_L stream is entirely unit-valued. It is an
arithmetic support mismatch, not an assumption of discrete-log hardness.

Several coefficient values per row, sums, ratios involving nonunit
numerators, different streams or row-dependent tops are outside (9).
Gaussian polynomials specialized where denominators are nonunit can
have zero-then-nonzero behavior after polynomial cancellation; (10)
cannot be licensed as an invertible prefix ratio there. Such algorithms
need their separately paid specialization/factor-recovery theorem.

## Exact consequence for the goal

The nearlinear selected-coefficient primitive remains valid, but it
cannot evaluate all changing-target rows by a single unit-normalized
coefficient lookup in a common unit-denominator stream. The theorem
does not exclude a more complicated transform combining those values,
a factor-only algorithm or an implicit norm evaluator.

Indeed the full-tag product on this family is already zero modulo N,
because it includes both exclusive rows. Returning that one saturated
gcd alone is not a factoring algorithm; the existing recovery controller
needs charged restricted queries or an equivalent informative payload.
The exclusive own tags in this proof remain private, and identifying
them cheaply is still open.

The general query bound remains soft O(m^(3/2)). No soft O(m) whole
query, all-semiprime sixth-rate factorization or Lean bit/memory
composition is supplied by this obstruction.
