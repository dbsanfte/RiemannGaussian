# Paid three-term projected sum families still lack proper-factor coverage

2026-10-08. Classical arithmetic proof by charged_engineering, with root's
selector-envelope and common monic post-exponent refinements. This concerns
new additive observations outside the frozen two-term order/kernel results.
No earlier report, source, artifact, journal or audit is changed. It is not
a lower bound for arbitrary factorization or an implicit long scalar norm.

## 1. Two concrete N-only observation families

Fix a finite catalog U of positive integer bases, independent of N. At a
public auxiliary prime m comparable to B=ceil(N^(1/6)), use the ORIGINAL
projection, with its exact input-dependent logarithmic exponent,

    ell_N=ceil(log₂(N+1)),
    S_(m,ell)=(m!)^ell,
    Gamma_(u,m)=u^((N-1)*S_(m,ell_N)) mod N.          (A1)

Fix also a constant finite library H_m of MONIC integer polynomials of
degree at most a fixed D. Each polynomial's coefficients may depend on m
but are fixed as N varies at that m, and have O(log m) bits. Constant 1,
h(T)=T, and h(T)=T-1 are allowed examples. No arbitrary N-dependent
coefficient selection is granted. The coefficient lists must be generated
deterministically in polylog(m) bit time; fixed constant polynomials satisfy
this contract. Put

    theta_(u,m,h)=Gamma_(u,m)^h(N) mod N.             (A2)

Signed powers and negative polynomial values use public unit inverses.
On the actual infinite family below all catalog bases are units.

The SAME-BASE family tests every u in U, h in H_m, and signed |e|,|f|<=L_m,

    theta_u^e+theta_u^f-1,  L_m=ceil(C*sqrt(m)*log(2m)^b). (A3)

This represents same-base three-term comparisons with a common exponent
origin removed: multiplying (A3) by any public unit theta_u^g restores
theta_u^(e+g)+theta_u^(f+g)-theta_u^g and preserves its exact gcd. The origin
g can depend on N; the two relative exponent labels must remain in the
stated complete menu. No original row target is silently replaced.

The MIXED-BASE family tests every u,v,w in U, h in H_m, and signed
|E|,|F|,|G|<=L_m, where now

    theta_u^E+theta_v^F-theta_w^G,
    L_m=ceil(C*m^(3/20)*log(2m)^b).                  (A4)

Bases may coincide and zero or negative exponents are included. Both
observations have coefficients (1,1,-1), so their value at three identity
elements is 1, rather than an identically saturated additive identity.

Permit every m in the previously reviewed first-K prime menu,
1<=K(N)<=floor(B^.020) eventually, including full-input adaptive selection
and all subsets/reorderings of these complete query families.

**Theorem.** On the SAME original actual balanced distinct-prime supply,
all observations (A3) and (A4), at EVERY allowed m and EVERY h in its fixed
library, are units modulo N after deleting respectively

    same-base family: soft O(M^5.5+K_*M^5.469),
    mixed-base family: soft O(M^5.950+K_*M^5.4345).  (A5)

Here X=M³ is the factor scale and K_*=O(M^.020) is the existing fixed
dyadic envelope. Thus the two new losses are soft O(M^5.5) and
soft O(M^5.950). Unite them directly with the existing soft M^5.994 loss
to retain Omega(M^6/log²M) actual inputs. Every new residual, subproduct
and mask product is a unit: these paid additive families cannot guarantee
a proper collision even if candidate selection is free.

Each COMPLETE new family is classically acquired in soft O(m) time and
space at a selected m. A fixed polylogarithmic auxiliary-prime menu costs
soft O(B) in total. The larger polynomial prime menu receives free coverage
access in the obstruction; no near-linear acquisition of that entire menu
is claimed. These are arithmetic failures of specified paid observations,
not successful examples, advisory finite groups or backend-only statements.

## 2. Exact original supply and candidate strips

Use the published-input supply preserved in the latest frozen audit
docs/semiprime-hensel-spectrum-obstruction-audit.json, SHA256
1b3e901b6527242662f0de0638eb56ee3156d40257ca900c4d173d469fa068ec.
For balanced primes P,Q in fixed bins [cX,X], X=M³, it has

    P-1=v_P*R_P,  Q-1=v_Q*R_Q,
    R_P>P^.677, R_Q>Q^.677,
    v_P,v_Q<=V=O(M^.969),
    R_P!=R_Q, R_P not dividing Q-1, R_Q not dividing P-1. (A6)

The actual original pair mass is Omega(M^6/log²M); the existing deletions
are counted on this original supply. The primary large-divisor input is
[Kurlberg--Pomerance, Lemmas 19--20](https://www.impan.pl/shop/en/publication/transaction/download/product/82225),
as already inspected and pinned in the frozen reports. No new prime-density
hypothesis, GRH or Quasi-Riemann Hypothesis is used.

Uniformly at every candidate, m=Theta(M) and v_P,v_Q<m<R_P,R_Q. With
K_* dominating all K(N), write G_m=m-p_(-K_*)(m). The frozen prime-menu
proof supplies the necessary selector implication

    p_(-K_*)(m)^6<N<=m^6,
    sum_m(G_m+1)=O(K_*M),   #comparable candidate primes=O(M). (A7)

Its BHP gap bound keeps all candidates and predecessors in one fixed
M-scale interval. At fixed P,m the candidate Q values lie in a real strip
of length

    D_(P,m)=O(M²*G_m).                              (A8)

Integer endpoints contribute the usual +1 in every residue-class count.
All possible comparable primes m may be included as a valid overcount;
there is no K multiplier in their O(M) total number. Equations (A7)--(A8),
not an independently advised selector, are used below.

## 3. Keep the full N-dependent exponent and vary the other factor

The exact ell_N in (A1) cannot be replaced by an uncharged constant.
However, N=P*Q remains in a fixed multiplicative M^6-scale bin. Hence
ceil(log₂(N+1)) assumes only O(1) values, independent of M. For each fixed
P,m, divide the Q strip according to those values. Within one such piece
ell is fixed and

    z_u=u^S_(m,ell) mod P,
    Gamma_(u,m)=z_u^(P*Q-1)=z_u^(Q-1) mod P.        (A9)

The last equality is Fermat's theorem in the P field. Since v_P<m,
v_P divides m!, so z_u^R_P=1. Thus every z_u lies in the unique subgroup
of order R_P, with order either 1 or R_P. No new omission-prime deletion
is needed for any fixed catalog base. If z_u=1, the same-base residual
is 1. This also handles the trivial base u=1.

For a monic h_m from the fixed library, P=1 modulo R_P gives

    k_h(Q)=(Q-1)*h_m(P*Q)=(Q-1)*h_m(Q) mod R_P.     (A10)

The right side is a MONIC polynomial in Q of degree deg(h_m)+1 between
1 and D+1. For every residue t modulo R_P, it has at most D+1 preimages,
because k_h(Q)-t is a nonzero polynomial over that prime field. This is
the paid, scoped mechanism for h(N)=N or N-1, despite their large values.
It does not permit unrelated N-dependent exponents or coefficients.

Within the fixed ell piece the actual post-projected values are exactly

    theta_(u,m,h)=z_u^k_h(Q) mod P.                 (A11)

The same statement holds in the Q field after exchanging the orientations.
Private P,Q,R_P,R_Q and all roots are proof-side variables only.

## 4. Same-base grid: a nonzero low-degree polynomial

Suppose z_u has order R=R_P. For a fixed signed pair (e,f), the relevant
Laurent polynomial is Z^e+Z^f-1. Multiplying by Z^L gives an ordinary
polynomial of degree at most 2L, whose value at Z=1 is 1. It is therefore
NONZERO over every hidden field, even when exponent labels coincide.
At most 2L elements of the subgroup can be its roots. Since z_u is a
generator, at most 2L exponent classes k modulo R give an additive zero.
By (A10), these have at most 2L(D+1) Q-residue classes modulo R.

An interval of length D_(P,m) contains at most D_(P,m)/R+1 integers in
each residue class. The O(1) ell pieces add only a constant. Thus a fixed
pair (e,f), fixed catalog base and h contribute at most

    O(L*(M²*G_m/R+1)) actual Q values at fixed P,m.  (A12)

The full pair menu has O(L²) members; use one envelope
L=O(M^lambda polylog M) for all public L_m. Count at most O(M³) choices
of P, allowing all integers for this upper bound, and use R>=c_R*M^2.031.
Equations (A7) and (A12) yield

    same-base bad ordered pairs
      =soft O(L³*(K_*M^3.969+M^4)).                (A13)

Both field orientations add a fixed factor. For lambda=1/2 this becomes
the first estimate in (A5), and eta=.020 leaves exponent 5.5 dominant.
No multiplicative-order zero-pattern invariance for additive sums is used.

## 5. Mixed bases: the zero indices form a Sidon difference set

Fix P,m,ell,h and one exponent/base tuple in (A4). Divide its residual
by the nonzero theta_w^G and put

    a=z_u^E*z_w^(-G), b=z_v^F*z_w^(-G), R=R_P.

Then a,b lie in the order-R subgroup, and the zero condition is

    a^k+b^k=1,  k=k_h(Q) modulo R.                (A14)

Let Z be the set of k in Z/R satisfying (A14), with cardinal s.
All degeneracies are explicit. If a=1 or b=1 the other term would have
to be zero, which is impossible for a unit, so Z is empty. If a=b!=1,
2a^k=1 has at most one solution because P is odd and a has order R.
The a=b=1 case has residual 1 as well.

Otherwise a,b and a/b have exact prime order R. For any h0!=0 modR,
two zero indices k,k+h0 give the two equations

    U+V=1,
    a^h0*U+b^h0*V=1,
    U=a^k, V=b^k.

Their determinant a^h0-b^h0 is nonzero, so

    U=(1-b^h0)/(a^h0-b^h0).

The value U determines k uniquely, since a has order R. Thus each
nonzero index difference h0 occurs for AT MOST ONE ordered distinct
zero pair. There are only R-1 differences, proving

    s*(s-1)<=R-1,  s<=sqrt(R)+1.                   (A15)

This elementary argument is consistent with the primary subgroup bound
in [Kelley--Owen, Lemma 2.3](https://arxiv.org/pdf/1510.01758v4).
Their theorem bounds trinomial roots in an order-R multiplicative subgroup.
Only its proved square-root bound is relevant; no conjectural logarithmic
prime-field bound or finite computation is used. The proof (A15) is supplied
here, so no discrete logarithms or subgroup generator are algorithm inputs.

By (A10) each zero class has at most D+1 Q preimages. Consequently one
tuple contributes, for each fixed P,m and O(1) ell pieces, at most

    O((sqrt R+1)*(M²*G_m/R+1))
       =O(M²*G_m/sqrt R+sqrt R+1)                  (A16)

candidate Q values. Use R>=c_R*M^2.031 and R<P<=X=M³. Summing P and m
with (A7) gives the EXACT two sources of loss

    one mixed tuple:
       O(K_*M^4.9845+M^5.5),
    all O(L³) tuples:
       soft O(K_*M^(4.9845+3lambda)+M^(5.5+3lambda)). (A17)

The second term uses #m=O(M), with no K multiplier. The first term uses
the folded gap sum and does include K. At lambda=3/20=.15 the loss is
soft O(K_*M^5.4345+M^5.950), yielding the second claim of (A5).
Library/base sizes and the bounded polynomial degree add fixed factors.

More abstractly, (A17) uses the cardinality of a Q-independent tuple
menu, not its exponent magnitude. A fixed list of T_m such tuples with
otherwise large exponents costs O(T_m) times the one-tuple bound, but its
bit lengths and numerical acquisition must be priced separately. No such
unbounded list is acquired for free by this report. The concrete (A4)
grid supplies a complete paid implementation instead.

## 6. Whole-family bit acquisition and proper-factor boundary

The implementation knows only N, m, the fixed base/polynomial libraries,
and their public exponent bounds. Compute ell_N exactly, construct m!
by a balanced integer product tree, and its ell_Nth power by binary
powering. Their output bit length, and the bit length of (N-1)*S, are
O(m logm log(N+1))=soft O(m). Fast integer multiplication and modular
binary powering compute the CONSTANTLY MANY Gamma_u in soft O(m) bit
time. The original equivalent staged projection is also available.

Each monic polynomial h_m has bounded degree and O(logm)-bit coefficients,
so h_m(N) and its bit length are computed in polylog(N) time and bits.
Its magnitude can be large; its bit length is O(logN). Modular powering
and public unit inversion compute the constantly many theta_u in
polylog(N) additional bit time once the projections are supplied.

Cache positive and negative powers through the relevant L_m. The same-base
menu has O(L_m²)=soft O(m) leaves; the mixed menu has O(L_m³)=soft O(m^.45)
leaves. Every query uses a constant number of O(logN)-bit ring operations
and one public gcd. Complete enumeration, scalar products, retained masks,
streaming and, if requested, all leaf output records fit soft O(m) time
and soft O(m) space. There is no pairwise row/baby matrix to construct.

For fixed polylogarithmic K, all m are comparable to B and repeat this
cost only polylogarithmically often. The previously paid BHP-bounded prime
generation and deterministic primality search fit soft O(B) as well.
For K=B^.020 the complete numerical acquisition is not claimed near-linear;
the all-menu arithmetic failure holds even when it is provided for free.

After the counted deletions, every residual is nonzero in BOTH fields,
so its gcd with squarefree N=P*Q is 1. Any product, mask, known-unit
rephasing or product-tree localization within these leaves remains a unit.
This is stronger than merely failing to obtain a proper gcd because of
saturation. It does not settle additional raw/cofactor tests, arbitrary
post-projection order consumers, or nonunit recovery outside this family.

## 7. Exact scope and remaining frontier

The SAME actual retained inputs defeat both new additive families and the
earlier registered repairs, because the new losses in (A5) are united on
the ORIGINAL supply before adaptive candidate choices. There is no claim
that arbitrary additive zeros share the old common-order seed invariant.
Fixed catalogs are essential to this count; a growing adaptive M^1.05
seed menu would have to pay its own union and acquisition costs.

This report does not evaluate the actual long residual norm, its ANY-zero
predicate, or a different resultant. It does not cover unrelated large
seed heights, coefficient libraries varying with the full N, unrestricted
three-term exponent grids, independent N-dependent exponents, new source
curves, arbitrary additive circuits, or arbitrary implicit scalar algorithms.
Monic common post-exponents h_m(N) are included only under the stated
fixed-library, Q-independent-coefficient and bounded-degree contracts.

No new OpenAI/math result is a premise of the proof. The prior targeted
catalogue assessment and mask-gcd appendix remain unchanged. No new Lean
theorem, source import, metadata entry, checker, generated C or validation
run is added. The new arithmetic and bit-acquisition bounds are classical.
Prime-square/nonunit/saturation recovery, routing/controller composition,
global bit time and peak memory for a guaranteed one-sixth factorization
algorithm remain unfinished. The complete goal remains active and unproved.
