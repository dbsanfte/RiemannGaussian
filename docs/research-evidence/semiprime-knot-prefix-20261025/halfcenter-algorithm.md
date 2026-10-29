# A one-sided native query and a knot at half the row rank

25 October 2026. Uniform, paid preprocessing and exact predicate reduction.
This gives a constant-factor reduction in the complete native query. Its
remaining cost is soft O(J+sqrt(JM)); no sixth-exponent algorithm is claimed.
Generic reciprocal folding and the previously proved native deletion
simplification are prior project credit. The contribution here is their
correct half-center application to the complete uncentered catalogue,
including the special rows, zero-only predicate, and one-sided recovery.

## 1. Paid preparation with all native rows accounted for

Use the existing scalar controller and complete catalogue: k=2*3^e,
H=k^2, N=PQ distinct odd primes, q=beta^H, and both beta local orders odd.
The hard branch gives ord_P(q),ord_Q(q)>16H, N>256k^4, k>16, and
2M+1<16H. Retain the original labels E=a+bN+lambda and all established
zero-row, diagonal, complete-swap and central screens. The central screen
either finishes or makes every x_j-1 a unit for x_j=beta^(E_j).

The known integer deletion analysis proves that b!=0 implies |E|>HM.
Only (k,0,H-k) and (-k,0,k) are deleted by public integer zero matching;
complete-swap pruning also removes their two vertical partners. Both pairs
of exceptions are stable under (a,b,lambda)->(-a,-b,-lambda mod H), as is
diagonal pruning. Thus the continuing catalogue is closed under this label
involution. This is an actual-family fact, not an assumption about arbitrary
row subsets.

If lambda=0, then 3^(2e) divides ab, because H divides 4abN and N is
coprime to k. Since 3^(2e)=k^2/4>k>|ab| on a nonaxis row, this is
impossible there. Hence only the four axis rows can have lambda=0. Query
these at the original full signed horizon using the established scalar
method, at cost soft O(sqrt(M)). A nonunit finishes through the existing
factor/annihilator consumer. Otherwise their full product is a unit, so
all their factors at every prefix are units and all four rows may be
removed without changing any prefix zero or nonunit predicate.

This unit certificate matters: combining separate **zero-only** predicates
for two classes by Boolean OR would miss a prefix with one prime's hit in
each class. We do not use that invalid class decomposition.

Every remaining row now has 0<lambda<H and a known opposite row

    E'=H-E,   y=q/x.

Choose one representative per label pair. There are L=J/2 pairs, where J
here denotes the row count after the preceding certified removals. Label
pairing is exact even if several numerical nodes coincide. The two central
screens certify both x-1 and x-q, because y-1=(q-x)/x. All this preparation
costs soft O(J+sqrt(M)), within the desired soft-k budget.

## 2. The exact one-point and prefix identities

Acquire

    W_j=x_j+q/x_j,
    G_h(W)=prod_(j=1)^L(W-W_j),
    D(t)=G_h(t+q/t)/G_h(1+q).

The denominator is a unit, since
1+q-W_j=-(x_j-1)(x_j-q)/x_j. The modulus has degree L, including
repetitions, and product-tree acquisition costs soft O(J). For every unit t,

    D(t)=prod_j (x_j-t)(x_j-q/t)/[(x_j-1)(x_j-q)].        (1)

Thus D(q/t)=D(t), and D(1)=D(q)=1. Let Delta_old(t) be the centered
Alexander normalization from the previous packet, built using every
remaining original row x_j and q/x_j. Then

    Delta_old(t)=D(t)D(t^-1)=D(t)D(qt).                  (2)

For A_m=prod_(i=1)^m Delta_old(q^i) and
B_m=prod_(i=2)^(m+1)D(q^i), B_0=1, equation (2) gives

    A_m=B_m B_(m-1)
       =D(q^(m+1))*prod_(i=2)^m D(q^i)^2,   m>=1.      (3)

Every factor in B_(m-1) also occurs in B_m. Therefore A_m is a nonunit
iff B_m is a nonunit, over any commutative ring. For the actual squarefree
N=PQ, A_m=0 iff B_m=0: the two products have the same zero support in
each residue field. This is a predicate equality, not equality of scalar
values. Removing multiplicities need not preserve zero modulo p^2.

This is the promised cancellation across native opposite rows. For one
pair it replaces the 4m original signed factors by the 2m factors

    prod_(r=-m)^(m+1), r!=0,1 (x-q^r)
       =x^m prod_(s=1)^m (W-q^-s-q^(s+1)).               (4)

The omitted r=0,1 factors are specifically certified units. Duplicated
interior collision factors are retained once, never inverted.

## 3. A negative-only prefix and a negative-only final scan

Let F(t)=prod_(all remaining rows)(t-x_j). Pairing gives

    F(t)=t^L G_h(t+q/t),
    D(t)=t^-L F(t)/F(1).

Using D(q^(i+1))=D(q^-i), the reduced prefix is exactly

    B_m = q^(L*m*(m+1)/2) / F(1)^m
              * prod_(i=1)^m F(q^-i).                  (5)

The multiplier is a known unit. Thus the original whole-family prefix
predicate equals that of the **one-sided** scalar query

    Z_m=[prod_(i=1)^m F(q^-i)=0 mod N].                 (6)

Coverage supplies Z_M=true and Z_0=false. Binary-search the first true m
using only these prefixes. The preceding scalar product is nonzero,
though it may be a zero divisor. A unit F(q^-m) could not annihilate it,
so F(q^-m) is a nonunit. Scan only

    gcd(x_j-q^-m,N)

over the remaining original rows. A proper gcd factors; a saturated leaf
gives beta^(E_j+Hm)=1 with a nonzero O(log N)-bit exponent by the original
public zero-row deletion rule. The existing licensed extractor applies.
Different prime witnesses may occur in different original rows; the full
scan retains them. No choice of a global trace sign is needed.

The current executable block method builds a degree-d geometric seed
polynomial and evaluates it at the actual J shifted targets per block.
Its cost here is soft O(J+d+Jm/d), optimized at d about sqrt(Jm) when
that lies in the allowed range, with residual blocks charged. The original
signed interval had about twice as many seed positions. This reduction
halves the seed count and the final signed scan; it leaves the asymptotic
exponent unchanged. The prefix primitive at soft O(J+sqrt(m)) is still open.

## 4. An ordinary Alexander polynomial with half as many trace nodes

The direct D is invariant under t->q/t. To give it an ordinary reciprocal
knot normalization without hidden nonunit divisions, acquire

    eta=beta^(H/2),   eta^2=q.

No extension is needed: H is even. Since both local beta orders are odd,
ord(eta)=ord(q)>16H locally. Screen x_j-eta, one test per opposite pair.
A proper gcd factors N. A saturated equality gives the licensed nonzero
annihilator E_j-H/2, unless this integer is exactly zero.

Handle that exception explicitly: an exact integer E_j=H/2 is a known
horizontal axis row (b!=0 has |E|>HM). Its opposite has the same exponent.
For every original |i|<=M,

    eta-q^i=eta*(1-eta^(2i-1))

is a unit, because 0<|2i-1|<=2M+1<ord(eta) at both primes. Delete those
two opposite rows; their removal preserves every prefix predicate. Do not
attempt to extract from exponent zero. There is no need to delete their
vertical swap partners or require subsequent swap closure: all deleted
leaves were certified harmless, and opposite closure remains intact.

On the continuing branch, rebuild G_h, F and D for this retained list;
its prefix predicates agree with the earlier list, although scalar values
need not agree. Let L now denote the remaining pair count and set
v_j=x_j/eta. Then v_j and v_j-1 are units, opposites are v_j^-1, and

    R(Z)=prod_(j=1)^L(Z-v_j-v_j^-1),
    K(T)=R(T+T^-1)/R(2).

The previous sparse Seifert construction acquires a genuine knot Alexander
polynomial reducing to K, with dimension 2L and at most 4L-1 nonzeros.
All coefficients and tests cost soft O(J). The earlier construction on J
original rows had dimension 2J. This half-rank statement uses the correct
center eta and paid exceptional branches; it does not assert inverse closure
of the original uncentered x_j list.

Since G_h(eta Z)=eta^L R(Z), the scalar
c=R(eta+eta^-1)/R(2) is a unit and

    K(t/eta)=c D(t),
    prod_(i=1)^m K(eta^(2i+1))=c^m B_m.                 (7)

Hence a product of this smaller knot's Alexander values along the odd
geometric progression eta^3,eta^5,...,eta^(2m+1) has exactly the required
zero/nonunit predicate. The long odd-stride product is still unpaid.

## Evidence and limits

The general proofs above supply the reduction and coverage preservation.
[halfcenter-review.md](halfcenter-review.md) independently reviews the native
pruning, all normalizations, predicate distinctions, and one-sided recovery.
[check_halfcenter.py](check_halfcenter.py) checks exact identities and CRT
branches on small rings; it is a reference calculation, not a fast oracle
or a native coverage experiment. The [row investigation](row-cancellation.md)
records the changed finite hypergeometric parameters and their costs.

The next required advance remains the same: acquire (6), or the equivalent
odd-stride knot product decision (7), in soft O(J+sqrt(m)). The present
result reduces concrete work uniformly, but does not establish that bound.
