
## Native moment actions and a complete cubic-cover alternative, 2026-10-24

The previous terminal pass initialized both coefficient ends, the true upper
Newton end, and the finite adjoint, but did not acquire the terminal
contraction in soft k. This pass uses the actual native roots and tests
arithmetic changes of the rows. It gives an acquired moment-stripe action
and a different complete covering algorithm of soft N^(2/9), conditional on
the already paid scalar preparation/recovery. The original whole query
still costs soft k^(3/2). The alternative is worse than the separate known
N^(1/5) factoring bound, and neither establishes the one-sixth goal.

The exact sources, independent reviews and append validator are in
`/tmp/semiprime-native-terminal-20261024`. Source normalization and degree
errors found during review were corrected by their authors before final
pinning. This is mathematical research; no finite example campaign or new
Lean backend lemmas are counted as an acquisition advance.

### Actually acquired native moment stripes

Retain the acquired native roots, their canonical phase carries, both
colours, and the correlated filter [Nu²]_H<2k. Choose one of the two
identical representatives per raw tag, preserving its original labels.
There are J0<=phi(k)<=k original rows. In the terminal notation J is the
actual degree of F AFTER optional reciprocal augmentation, so J<=2k.
With m=k, Q=q^m, and G=2k for the original main prefix (3k for the repaired
one), the monic polynomial

    R(T)=prod_(j,g<G)(T-Q^g y_j)

has degree D=JG<=4H (respectively 6H). Each actual last-two tail is kept
separately. If duplicate filter representatives are intentionally retained,
the augmented bounds instead are 8H and 12H; both remain below 16H.
Do not mix those cardinality conventions when checking unit margins.

For any supplied a<m, acquire z_j=y_j^m and w_j=y_j^a, and construct the
actual rational function

    H_a(Z)=sum_j w_j/(1-z_j Z).

Its denominator and numerator are acquired by fraction-addition trees.
The denominator has constant one; its first O(k) series coefficients give
ALL p_(a+mr)=sum_j y_j^(a+mr) along that stripe, through the desired long
index, in soft k. No root-difference inverse or free far-coefficient oracle
is used. For the reshaped matrix P[r,a]=p_(mr+a), an arbitrary supplied
vector v is applied by evaluating V(X)=sum_a v_a X^a at the acquired y_j,
then reusing the weighted rational expansion. This gives actual P and P^t
actions in soft k. These are standard supplied-root rational primitives;
their use here does not claim a special native Gauss-sum theorem.

The authoritative monic normalization is crucial. With r0=R(0),

    log(R(T)/r0)
      =-sum_(n>=1) bar_p_n S_G(Q^(-n)) T^n/n,
    bar_p_n=sum_j y_j^(-n), S_G(X)=1+...+X^(G-1).

Positive-root moments would describe the REVERSED polynomial instead.
The corrected algorithm reacquires the inverse-root stripes with poles
y_j^(-m) and weights y_j^(-a). For each stripe, acquire S_G and its actual
values at Q^(-(a+mr)) by monic MPE. Divide only by positive integers n<=D;
clip padded entries n>D, and set the n=0 logarithm coefficient to zero.
This acquires one complete q-log stripe in soft k, without pretending
1-Q^n inverses are free. All stripes, formal exponentiation and the final
short remainder cost soft D=soft k², a valid zero-safe completion but
slower than the retained blocked query.

Before the integer integration factor, the weighted transform is

    W[r,a]=bar_P[r,a] S_G(Q^(-(mr+a)))
          =sum_(g<G) Q^(-mrg) bar_P[r,a] Q^(-ag).

A G-term execution uses the acquired bar_P action G times. The direct
interpretation has the shifted inverse-root grid Q^(-g)y_j^(-1).
The nonlinear exponential also mixes residue stripes through carries.
Thus the cheap unweighted action does not yet provide the weighted
nonlinear terminal contraction. Nor can the native quadratic phases be
treated as additive characters: pi^H=q, not one, and shifting u retains
actual q carries and the sparse low-a Hensel selection. Each fixed-a
fiber has at most 16 roots, but summing Theta(k) such fibers recovers the
same degree-J moment denominator.

### Public lift normalization and its actual horizon

For original tag data a,b,ell,delta and an integer lift s>=0, define

    a_s=a+ks, b_s=center_k(b+sj),
    z_s=(b+sj-b_s)/k,
    ell_s=ell-ksj-Hz_s,
    delta_s=delta+ks(1-j)-Hz_s.

The exact shared target formula is

    V_s=V_0 [beta^(k(1-j)) W^(k(chi(j)-j))]^s q^(-z_s),
    I_s=I_0+s(P-j)/k-z_s.

Let g=gcd(j-1,k), r=[delta]_k and d=(delta-r)/k. One public congruence,

    s(1-j)=[d]_g-d mod k, 0<=s<k/g,

acquires a canonical scalar phase delta_*=r+k[d]_g in [0,kg).
Divide the congruence by g before taking a modular inverse. The actual
normalization is a q power, not a discarded carry. Its own index is

    I_*=[a_s(P-1)+Q+delta_*]/H,
    0<I_*<k³/g+H/16+1.

The smaller phase strip can therefore require a LONGER clock. For small
g its norm-saturated factor-sum difference can have size k^5/g; the old
O(H²) decoder margin cannot simply be reused. A longer order screen can
be paid using the actual rough scalar bridge, but it does not restore
that factor-sum bound or improve the clock. A completely legal hybrid
replaces only g>=k/2 classes (s<=1, constantly many tags) and retains the
original parity rows elsewhere. It has the existing 3H+2 horizon and
consumer, and the same soft k^(3/2) whole-query cost. This is not a generic
obstruction to other lift constructions.

### Primitive small-root calculation, with both content factors removed

At the own tag write P=j+kx and Q=q0+ky, q0=[N j^-1]_k. The primitive
bilinear integer equation is

    f(x,y)=kxy+q0 x+jy+(j q0-N)/k=0.

For a factor-size bin S, X~S/k and Y~N/(Sk) give XY~N/k² and weighted
height W~N/k. Coppersmith's separate-degree-one sufficient bound
XY<W^(2/3) therefore needs k>N^(1/4), not N^(1/6). Keeping the removed
factor k in the height would produce the spurious sixth threshold.

The native relation gives y=kI-a x-s0, with exact public s0, and removes
another factor k:

    f(x,kI-a x-s0)=k g(x,I),
    g=(j+kx)I-a x²-bx-c_j, c_j=(d_j+j b)/k.

This primitive g has TOTAL DEGREE TWO. With the actual full coordinate
bounds, W_g~(N+aS²)/k² and X Y_I~(N+aS²)/k³. Even the stronger
Coppersmith total-degree-two condition X Y_I<const sqrt(W_g) fails by
at least a factor of order sqrt(N)/k². The integrality of I is exactly
PQ=N modulo k² in these coordinates; it is not an independently known
residue of P modulo k².

The univariate unknown-factor lattice is also explicit. For the monic
f0(X)=X+j k^-1 modN, use N^(t-i)f0^i (i<t) and X^l f0^t (l<s), dimension
d=t+s. After column scaling by the root bound X, its determinant is
N^(t(t+1)/2) X^(d(d-1)/2). The LLL/norm integer-vanishing certificate at
P>=N^beta requires X<N^(beta²) with exponent slack. The exact finite-d
optimization gives an even smaller exponent. The native X has exponent
beta-1/6, strictly larger than beta² for every beta in [1/3,1/2].
These are failures of specified sufficient certificates on the full
boxes, not impossibility theorems for lattices or occasional short vectors.
Primary Coppersmith and Howgrave-Graham sources are cached and pinned in
the packet; multivariate extraction independence is never assumed.

### A complete alternative cover using cubic weights

The new construction changes the input family; it does not accelerate
R mod P_m for the old one. It uses the already acquired scalar beta with
odd k-rough local orders>16H and the seed q_c=beta^(k³). Its local orders
are unchanged. No angular target or character is needed for this new
scalar family because its collision exponent has a factor P-1 directly.

For each public unit j modulo k, acquire the rank-three lattice

    b+3aj=0 modk,
    cN-2aj³-bj²=0 modk².

Its displayed triangular basis has determinant k³. Choose
ell0=-a j²-bj-cN j^-1 modk³. Then
f(X)=aX³+bX²+ell0 X+cN vanishes modulo k³ on EVERY X=j modk.
Consequently the own index (aP²+bP+cQ+ell0)/k³ is an integer.
Degenerate vectors a=0 are allowed and handled, not silently excluded.

In a public interval |P-P0|<=Delta<=P0/2, let F(X)=aX²+bX+cN/X.
Apply the exact rational linear map

    (a,b,c) -> (Delta F'(P0),
               Delta²(a+cN/P0³), Delta³ cN/P0^4).

Its determinant is N Delta^6/P0^4. Fixed-dimensional LLL on the acquired
rational lattice (after clearing denominators) gives
||w||_infinity<=sqrt(2) k N^(1/3) Delta²/P0^(4/3). Choose a public common
upper bound T as in the report. The exact Taylor remainder proves
|F(P)-F(P0)|<=4T. This is a guaranteed short-vector upper bound, not a
lower bound or a heuristic independence claim.

The public integer floor nu=floor((ell0+F(P0))/k³+1/2) centers the index.
With U=ceil(1/2+4T/k³), set ell=ell0-k³nu+k³U,
E=a+b+ell+cN and h=2U+1. The own index i is in [0,h), and

    E-k³i=(P-1)[cQ-a(P+1)-b].

All signed exponents and centering metadata have O(log N) bits and are
actually acquired. Before querying, test integer roots of the nonzero
quadratic aX²+(a+b)X-cN for proper divisors of N. This handles every own
ZERO integer exponent. Next remove any row with a public zero position
E=k³z, 0<=z<h. Because ord_P(q_c)>h, such a row could be the own row only
if its own index were z, already handled by the quadratic precheck.
This ordering is essential to retain coverage and exclude zero K.

For dyadic S<=P<2S, choose Delta within a constant factor of
k S^(7/9)/N^(1/9), with public integer cutoffs. Acquire every tag at every
needed interval centre. A common clock and the complete number of rows
both satisfy

    J_S,h=O(N^(1/9) S^(2/9))<=O(N^(2/9)).

Uniformly, h<16H for sufficiently large N. The public guard is checked;
trial division handles the finite exceptional range. Acquire the actual
h-factor polynomial prod_(i<h)(1-q_c^iY), evaluate it at all retained
V^-1=beta^(-E) by monic MPE, and scan gcds. A saturated row is localized
by at most h explicit leaves. Each retained leaf supplies either a proper
factor or a GLOBAL NONZERO annihilator K=E-k³i. The inherited short
annihilator extractor, exact source pin in the report, costs soft k;
the bounded factor-sum decoder is never used here.

The resulting complete promised-branch cost, including lattice vectors,
root prechecks, starts, row outputs, localization and recovery, is
soft N^(2/9)=soft k^(4/3). Previously paid soft-k scalar preparation
composes without increasing it. This is a proved alternative tradeoff
between more rows and a shorter interval. It improves this branch's old
k^(3/2) construction, while remaining slower than the established fifth
benchmark. The universal one-sixth acquisition and full executable/Lean
bit proof remain open.

### Single terminal resultants and the precise nonlinear norm batch

A second initialized representation avoids the JG composed-product vector
for ONE terminal value. Acquire Gamma_G(Z)=prod_(g<G)(Z-Q^g). For an actual
unit t, acquire H_t(X)=X^G Gamma_G(t/X), a degree-G polynomial whose
coefficients are gamma_d t^d. Then, exactly,

    R(t)=Res_X(F,H_t)=prod_j y_j^G Gamma_G(t/y_j).

The acquired polynomial arrays and one fast resultant cost soft(J+G).
Every quadratic-algebra pivot is classified as factor, unit, or ACTUAL
global zero: a saturated norm forces both coordinates to vanish at the
nonsplit prime, so their integer gcd gives a proper factor or global zero.
This permits lawful degree drops and unit divisions in fast resultant
arithmetic. A nonunit final value is localized by splitting the larger of
the root and orbit subsets; the total degrees along that path decrease
geometrically, giving the same soft(J+G) localization cost.

At t_i=q^(-i), a native leaf is a known unit times V_j-q^(mg+i).
A reciprocal-augmented leaf uses the original reverse index
L0-1-(mg+i); both are MAIN indices. Actual last-two tails stay separate.
Independent evaluations at all m nodes cost soft m(J+G)=soft k².

The more specific sharing target uses E=B[X]/F, xi=X modF and the actually
acquired inverse v=xi^-1. With u_X=Norm(xi)=(-1)^J F(0),

    R(t_i)=u_X^G Norm_E(Gamma_G(t_i v)).

The input arrays have total size O(J+G+m). The inner composition v,F is
fixed; the outer coefficient vectors differ only by gamma_d t_i^d.
What is required is the batch of m SCALAR norms, or its product with
restriction support, without necessarily producing m rank-J residues.
Transposition of modular composition only supplies linear projections;
the norm is nonlinear. Neither an output-size lower bound nor a fast
norm-batch algorithm follows from that distinction.

Primary Bostan--Flajolet--Salvy--Schost composed-product algorithms really
acquire the full degree-JG result, at soft JG. Kedlaya--Umans legitimately
has finite composite-ring extension scope, but its explicit modular
composition, power-projection and evaluation-preprocessing contracts do
not supply this implicit nonlinear norm batch. Their actual inputs and
rank costs are charged in the report. The fixed-inner formulation is an
initialized research target, not an achieved rate improvement.
