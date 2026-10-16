# Low-degree weighted q-shifts do not descend on the actual source carrier

2026-10-16. Exact actual-source obstruction to fixed-carrier weighted monodromy. It does not exclude interpolation/compression on canonical representatives, fixed-input syzygies, rational gauges with charged poles, or a general fast query algorithm.

## 1. Precise descent contract

Work first in a hidden field K. Let H(t)=product_(i=1)^J(t-z_i) have distinct nonzero roots, q!=0, and w=A/B with B coprime to H. Thus w is regular at every source node and its denominator is a unit in K[t]/H. Define on polynomial representatives

    U_w f = w(t) f(qt) mod H.

This rule is independent of the chosen representative f modulo H if and only if

    H(t) divides A(t) H(qt).                      (1)

Necessity follows by applying the rule to H, which represents zero. Sufficiency follows because every representative change is H g and its shifted change is H(qt)g(qt). The unit denominator can be canceled in this criterion. Equivalently, at every node,

    A(z_i) H(qz_i)=0.                             (2)

If an apparent pole in a displayed A/B is removable, first cancel it or use a regular presentation. GENUINE poles at source nodes do not define this operator on the whole value quotient; finite parts and derivative regularization are different contracts.

A compressed interpolation operator on the canonical degree<J representative always exists. Failure of (1) does not invalidate that paid operator; it prevents identifying it with the representative-independent action of U_w on arbitrary polynomial classes, as would be needed to import an unrestricted rational monodromy proof.

## 2. Actual dangling-node count and degree obstruction

Publicly deduplicate equal literal integer offsets. Use J for the remaining node count, so (m-1)/2<=J<=m-1. The source is

    z_i=gamma^(-N-delta_i), q=gamma^d, d=m^2,
    -3d<=delta_i<=d,
    delta_j=N(t_j^2-2t_j) mod m, t_j=j^(-1).

The last quadratic has at most two original tag preimages per residue because m is prime and N is a unit modulo m. The actual local orders of gamma exceed 16d. Consequently

    qz_i=z_j in either field
       iff delta_i-delta_j=d as an INTEGER.       (3)

Indeed the difference delta_i-delta_j-d has absolute value at most 5d, less than either order. Distinct deduplicated nodes have unit differences; the adjacency relation is identical in both fields.

Every directed adjacency in (3) stays in one residue class modulo m, with at most two nodes. Such a class contributes at most one directed edge and cannot contain a three-node chain. Thus at most floor(J/2) nodes have a successor in the supplied set. The dangling set

    D={i:H(qz_i)!=0}

has cardinal at least ceil(J/2), in BOTH fields. At dangling nodes H(qz_i) is a unit modulo N; at the other nodes it is zero modulo N, by the same integer criterion.

Criterion (2) requires a descending weight numerator to vanish at every dangling node. Therefore every NONZERO field numerator A permitting descent has

    deg A>=|D|>=ceil(J/2).                         (4)

If A is the zero field polynomial then the weight is already the zero operator there. In a composite-ring statement one applies this distinction separately in each field; a nonzero polynomial over Z/N is not automatically nonzero after both reductions.

For the normalized operator weight

    w(t)=(1-t)/(1-a t), a=q^L,

the delta-unit branch makes its denominator a unit modulo H. Its nonzero numerator has degree one, so descent fails for J>=3 on the ACTUAL catalog. This closes the weighted-descent caveat for this specific branch without a new deletion or generic-specialization argument.

## 3. Exact boundary-map rank and unit-row support

For any regular weight, consider representative changes H g with deg g<J. Their missed quotient values are

    (U_w(Hg)(z_i))_i
      =diag(w(z_i)H(qz_i)) (g(qz_i))_i.           (5)

The evaluation map g->(g(qz_i)) is invertible because the qz_i are distinct. Hence the defect map in (5) has EXACT rank

    #{i:w(z_i)H(qz_i)!=0}                         (6)

over the hidden field. This is not merely a factorization upper bound.

The inherited retained-family unit-row theorem leaves J-o(J) nodes where F(z_i)=P_L(z_i;q) is a unit in BOTH fields. If the weight is nonzero there fieldwise (in particular, if it is a unit modulo N there), (6) is at least J/2-o(J). Conversely any weight that DOES descend must vanish on at least J/2-o(J) of these unit rows, and so cannot act as a zero-support-preserving multiplier there. For the specific normalized weight, at most one dangling node can be canceled by 1-t; its defect rank is at least ceil(J/2)-1, regardless of whether a node equals 1.

Thus a universal linear boundary-correction representation for arbitrary polynomial g needs Omega(J) independent linear boundary data when the weight preserves the unit rows. This is a finite-dimensional rank theorem for that contract. The defect itself may still have fast actions, and a fixed F can possess special syzygies; no arithmetic-operation or universal query lower bound follows.

The same criterion gives a finite-jet extension. On K[t]/H^s, with s>=1 and B coprime to H, descent is equivalent to H^s dividing A(t)H(qt)^s. At every dangling node H(qz_i) is nonzero, so A must vanish there to order at least s. Thus the weight kills the ENTIRE source s-jet at every such node for any shifted payload regular there; a nonzero numerator has degree at least s|D|. Increasing a homogeneous fixed-carrier jet precision therefore retains the same loss of the Omega(J) unit rows, rather than repairing it. Pole-bearing payloads, inhomogeneous boundary terms and global reconstruction remain different contracts. No precision-dependent operation lower bound is inferred.

## 4. Exact chain classification for numerator 1-t

More generally let q have finite order R>J, and let a nonempty set of J nonzero nodes satisfy H|(1-t)H(qt). Each component of the successor graph x->qx is a chain or a full q-cycle. A full cycle has R nodes and is impossible. Every chain has a dangling terminal node, and condition (2) forces that terminal node to be 1. There is only one such node, so there is exactly one chain:

    {z_i}={1,q^(-1),...,q^(-(J-1))}.              (7)

Conversely this set satisfies the condition. For J<=L<R, all these nodes are roots of F=P_L. The actual catalog with J>2 cannot have this chain because all chain offsets would lie in one two-element low-digit fiber. The actual many-unit-row condition also excludes it. This classification concerns regular weights with numerator 1-t, not arbitrary pole-bearing q-equations.

## 5. Gauges: the real escape and its boundary cost

A rational gauge can change the weight to

    w_new(t)=w(t)G(qt)/G(t),

while changing the payload to F/G. If G is a unit at the source AND at all q-source points under consideration, this change keeps w_new nonzero on the same unit rows and cannot repair the descent obstruction. It does not make the dangling-node problem disappear.

If G is only a unit at source nodes, zeros at q-source points can indeed create zeros of w_new at dangling nodes and force descent. That possibility is NOT excluded. On the normalized delta-unit branch, however, at a source UNIT row one has 1-z_i!=0 (since F(1)=0), and the exact q-difference relation gives

    F(qz_i)=[(1-a z_i)/(1-z_i)]F(z_i)!=0.

Therefore a gauge zero G(qz_i)=0 used to kill such a dangling unit row makes F/G have a genuine pole at that successor point. Repairing all dangling unit rows in this way produces poles at Omega(J) distinct successor points. A pointwise zero times an infinite payload is not an ordinary value computation; the cancellation requires a separate rational/finite-part/residue treatment. A succinct rational representation might still handle those poles cheaply. This is not a pole-count operation lower bound or a proof against all rational gauges.

## 6. The cheap normalized operator still has an unpaid actual boundary

The connection to the spectral check is exact. For w=(1-t)/(1-a t), the q-factorial identity says U_w F=F rationally. Let Q be the column-value interpolation q-shift and U_H=diag(w(z_i))Q its canonical compressed operator. On the delta-unit branch,

    det(I-U_H)=phi(1)/delta,
    phi(1)=h_0 product_(s=0)^(J-1)(q^L-q^s),
    delta=product_i(1-a z_i), h_0=H(0).

This follows from the normalized companion pencil, or direct determinant expansion; the row/column operators are transposes. The numerator is a unit on the actual branch because h_0 is a unit and 1<=L-s<=L when J<=L. Thus I-U_H is invertible, even though the actual F has forced collision values and many unit values.

Write F=r+H G with deg r<J and f_i=F(z_i)=r(z_i). The correct equation is

    (I-U_H)f = (w(z_i)H(qz_i)G(qz_i))_i.          (8)

This follows by inserting F(qz_i)=r(qz_i)+H(qz_i)G(qz_i) into U_w F=F. Discarding the right boundary would falsely force f=0, contradicting the actual unit rows. The boundary is not identically zero on this source. No claim is made that its entries are dense for this fixed G: the rank theorem (6) concerns arbitrary representative changes. A fast inverse for I-U_H would still need the forcing vector, whose acquisition contains the unpaid quotient tail. Neither the cheap operator nor its invertibility is the long-query algorithm.

## Scope and prerequisites

The source bounds, two-fiber theorem, exact local-order premise and unit-row density are pinned in weighted-descent-source-pins.json. No new analytic supply/counting assumption is introduced. The result excludes importing the uncompressed rational weighted-q monodromy as a regular, support-preserving fixed-carrier action on this actual source. It does not exclude the paid finite-block interpolation q-pencil, compressed iteration on canonical representatives, special syzygies of the fixed q-binomial input, nonlocal rational reconstruction or general factor-only acquisition. No repository edits, builds, examples or new Lean declarations were used.
