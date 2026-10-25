
## Implicit coefficient extraction and fast reshaped recurrence action, 2026-10-24

This continuation supplies actual sublinear coefficient access and a fast
matrix-vector action for the geometric-product recurrence. It does NOT
supply the whole native collision query at soft k. The complete guaranteed
query still costs soft(J+sqrt(JL))=soft k^(3/2), J=Theta(k), L=Theta(k^2).
The one-sixth theorem and complete executable/Lean bit composition remain
open. No arbitrary-semiprime coverage or original-label recovery is replaced.

Let B be the acquired constant-rank quadratic algebra, q the ACTUAL
rescreened coupled seed, C=16k^2 and L=2k^2+2. All 1-q^r through C are
certified units. For b<=L write

    P_b(X)=prod_(i<b)(1-q^i X)=sum_(n=0)^b c_n X^n,
    f(n)=prod_(r=1)^n(1-q^r),
    c_n=(-1)^n q^[n(n-1)/2] f(b)/(f(n)f(b-n)).

The exact original block conversion is

    prod_(r<b)(V_j-q^(ab+r))=V_j^b P_b(q^(ab)/V_j).

Every V_j is a certified unit. For L=A b+d, the full product uses the
K=JA actual full-block arguments q^(ab)/V_j and the original d-term
last blocks. All labels, known unit factors, tails and original restrictions
remain part of a completed query. Auxiliary coefficient-mask zeros are
not original factoring witnesses.

**Paid selected prefixes and clock values.** ANY T requested f(n),
0<=n<=b, cost soft(sqrt b+T). Acquire all dyadic short block polynomials
B_h(Y)=prod_(r=1)^h(1-q^rY) through h~sqrt b by shifted doubling. One
monic MPE and prefix multiplication supplies all full coarse blocks.
For each requested unaligned tail, use its binary decomposition: one MPE
per dyadic size acquires at most T actual shifted starts. Total polynomial
size is soft sqrt b; total requested-tail work is soft T. This construction
uses no division. The q-unit certificates justify the later coefficient
formula, yielding any t selected c_n in soft(sqrt b+t).

A fixed Schoenhage inner digit mask has at most sqrt D positions in
radix dimension D=4^m. Thus when D=Theta(b+1), its exact weighted sum
costs soft sqrt b, including non-parity masks. For ONE fixed mask of
support t at consecutive arguments x0*Q^g, acquire d_n and lambda_n
and the rational series sum_n d_n/(1-lambda_n T). An actual fraction
tree and constant-one series inverse produce ALL R requested consecutive
values in soft(sqrt b+t+R), even with repeated bases or zero sums.

**Stronger dense action.** Reshape the coefficients with a width
D~sqrt(b+1), H=ceil((b+1)/D), padding the final row with zeros:

    M[rho,r]=c_(D rho+r) x^(D rho+r),  0<=r<D.

For ONE supplied vector v of length D, all H entries of M v can be
computed without acquiring the H*D coefficients. For full rows, put
U=q^(D rho). The exact cleared adjacent-coefficient relation is

    (1-q^(r+1)U) M[rho,r+1]
          =x(q^b-q^r U) M[rho,r].

Consequently each row dot product equals its acquired start
c_(D rho)*x^(D rho) times the SAME rational Newton expression

    F(U)=sum_(r<D) v_r
                  prod_(h<r) x(q^b-q^h U)/(1-q^(h+1)U).

Its degree-O(D) numerator/denominator are acquired by a prefix-product
sum tree: with block triples (P,Q,S), where S/Q is the local weighted
prefix sum, merge using

    P=P_left*P_right, Q=Q_left*Q_right,
    S=S_left*Q_right+P_left*S_right.

Use (1,1,v_(D-1)) for the final tree leaf: the last unused transition
is omitted. The denominator then uses only h<D-1. For every full row,
its factors have exponents at most D*rho+D-1<=b. Actual coefficient work
is soft D. MPE at the H real row starts and unit denominator division
costs soft(D+H). The selected-prefix routine acquires all row-start
coefficients in soft(sqrt b+H). Acquire the last partial row's at most D
coefficients with that same routine and take its dot product explicitly;
no extended order guard is needed. The resulting complete action costs
soft(sqrt b+D+H), hence soft sqrt b for balanced D,H. It permits nonunit
x and zero outputs: no entry of M or final row sum is inverted.

Any supplied separable row/column weighting u_rho*v_r now contracts
in the same budget. In particular a product of arbitrary radix-four
digit weights splits at a radix cut and can be dense; it need not have
the sparse singleton/pair support used in the first primitive. This is
an exact structured matrix-vector algorithm with paid initialization,
not a claim of low ordinary rank for the coefficient array.

The same acquired action has a paid transpose: the row starts, fixed
polynomial blocks and inverse denominator values do not depend on v.
Reverse the linear numerator-tree/MPE circuit with fixed multipliers,
including the explicit last-row coefficients. This computes M^T u in
soft(sqrt b+D+H) for ONE supplied outer vector u; no component of u is
inverted. For D=4^m, then apply the six-by-four singleton/negative-pair
mask map in each radix digit. The intervening arrays have geometrically
increasing sizes, so ALL 6^m inner left masks for this same outer vector
cost soft(sqrt b+D+H+6^m) JOINTLY. With D,H~sqrt b this is
soft(b^[log_4(6)/2]), approximately soft b^0.6463, and every returned
mask value is charged. It is not 6^m separate square-root computations.
Balanced D here is a choice for this standalone coefficient-array
primitive; the paper's actual thin inner dimension need not be balanced.
The fixed outer vector condition is essential: the source tensor's
active-Q/grid assignments also change the outer weighting.

ONE fixed-Q complete coefficient-band summand, including its outer
ternary box, also costs soft sqrt b. Bounded b is handled directly.
Its aligned mixed-radix block has
length B0=4^m*3^(h-m). If B0>=sqrt b, choose a digit-boundary width D0
between sqrt b and 4sqrt b; D0 divides the block offset in the actual
band layout. All digit weights separate across that cut into explicit
row/column vectors of length O(sqrt b). The dense action applies. If
B0<sqrt b, acquire the at most B0 contributing coefficients directly.
This improves the separate AP-box bound for that individual summand;
the sum over different Q and the wanted full-leaf union remain unpaid.

The original evaluation P_b(y) requires the paired moving weights
u_rho=y^(D rho), v_r=y^r (take x=1). BOTH weights change at each native
target y. A fast matrix-vector action for one supplied v therefore does
not yet compute all those diagonal bilinear forms, or their restricted
product, at the same cost. That simultaneous contraction is the concrete
next algorithmic target; generic matrix-vector access does not supply it.

**AP boxes and the tested tensor route.** For ONE x and ONE residue a
modulo any stride D, T requested prefix sums of c_(a+D rho)*x^(a+D rho)
cost soft(sqrt b+T). For D<=sqrt b, the coefficient ratio has numerator
and denominator degree D; an actual order-two matrix block algorithm
uses length~sqrt b/D, degree~sqrt b and dyadic tail refinement. A sum
ending at n uses transitions only through n, then adds its last term;
the total denominator is the unit f(n)/f(a). For D>sqrt b, acquire the
fewer than sqrt b+1 coefficients explicitly with the selected-prefix
routine. This yields actual row-box sums without dense expansion, but
sharing across different residues or different x must still be charged.

The [Alman--Vassilevska Williams tensor](https://arxiv.org/abs/2610.06783)'s exact inner masks are singleton or
negative-pair radix-four masks. Its outer masks also sum ternary row
boxes, and its real input encoder sums many active inner-position sets
Q with different block offsets. With only one active Q, pair leaves
have zero on the opposite side: the bilinear identity collapses to the
ordinary matching singleton products. Its batching saving requires the
multi-Q interactions. For m>=1, the unmodified full preencoding writes
10^h entries per band, h=19m, exceeding the actual coefficient-band input
size; an implicit improvement must acquire a suitably smaller/shared
wanted-form union, not execute that full phase and omit its cost.

Two exact output reductions were attempted. Coefficient reshaping followed
by thin multiplication asks for ceil((b+1)/D)*K partial outputs, before
weighted column contraction. Folding each target's high powers first
reduces the wanted outputs to K diagonal entries but leaves those
native target-weighted inputs unacquired; ordinary square preprocessing
also exceeds the desired budget. These counts reject those explicit
completions, not all implicit or recurrence algorithms.

Reports and exact independent reviews are in
`/tmp/semiprime-implicit-thin-encoding-20261024/`. The positive primitives
are proved over the composite ring, with starts and denominator guards
included. No examples, backend expansion, general lower bound or new
whole-family exponent is asserted. The next substantive task is to
share the paired moving-vector contraction across all original targets,
while preserving the original bounded-leaf localization contract.
