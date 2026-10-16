# Finite-grid adjoints: boundary residues carry the query, while selected coefficient jets are cheap

2026-10-15. New exact finite-grid and deformation identities, with a positive selected-jet primitive. No soft O(m) actual weighted evaluator was obtained. These results do not invoke the earlier exact rational-function solvability obstruction and do not exclude interpolation or regularization algorithms in general.

## 1. Ring-safe finite-grid setup

Work over R=Z/N. Assume gamma,u are units, d>=1, q=gamma^d, L>=1, and all 1-q^r for 1<=r<=L are units. Put

T(p)(x)=(1-x^d)p(x/gamma)-u(q^L-x^d)p(x),
E(x)=sum_j w_j x^(e_j),
f_k=u^k c_k,  P_L(Z;q)=sum_(k=0)^L c_k Z^k.

The wanted formal weighted query is

S=sum_(k=0)^L f_k E(gamma^k)=sum_j w_j P_L(u gamma^(e_j);q).

The recurrence is f_0=1 and

(1-q^(k+1))f_(k+1)=u(q^L-q^k)f_k.

For 0<=k<=L every f_k is a unit, since its numerator and denominator products use only nonzero powers 1,...,L. In the actual retained source d=m^2, u=gamma^(-N-3d), e_j=3d-delta_j, L<=4m^2, and the hidden prime orders exceed 16m^2. Therefore the unit hypotheses hold in both fields and modulo N without knowing those orders numerically. Also d is a unit. The actual density theorem supplies m-o(m) unit row products, so the formal polynomial S is nonzero in each hidden field. This is a promise-side application, not an unconditional certificate for arbitrary q.

## 2. What arbitrary pointwise interpolation can and cannot change

Write a_k=1-q^k and b_k=-u(q^L-q^k). On the sampled points, an everywhere finite p must satisfy

 a_k p_(k-1)+b_k p_k=E_k, 0<=k<=L,
 E_k=E(gamma^k).

Here a_0=b_L=0. There are L unknown sampled values p_0,...,p_(L-1), L+1 equations, and all b_0,...,b_(L-1) and a_1,...,a_L are units. The cokernel is exactly one free R coordinate: the left null vector f_0,...,f_L. Thus there exists a polynomial interpolant satisfying ALL these equations iff S=0; equivalently, the unique degree<L interpolant through the values forced by the first L equations satisfies the final equation iff S=0. This is a finite matrix statement, not a rational-function identity claim.

More explicitly, eliminating equations 0 through k gives

 p_k=[sum_(r=0)^k f_r E_r]/(f_k b_k),  k<L.

After solving the first L equations, the final defect is

 E_L-a_L p_(L-1)=S/f_L.

This shows exactly where a proposed one-omitted-equation interpolation construction places its payload: its final defect already is the wanted weighted sum up to a known unit. It does not prove that this defect is expensive to acquire by another method. If some equations are omitted or paid anomalies introduced, they must be retained in the query formula.

The points gamma^0,...,gamma^(L-1) have unit pairwise differences on the actual source. Consequently every vector p_0,...,p_(L-1) has a unique degree<L interpolation polynomial over R. This existence fact does not supply a sublinear interpolation/evaluation algorithm: explicitly acquiring that vector costs L entries. No degree-versus-operation lower bound is used.

## 3. Boundary poles really escape the finite-value matrix, with an exact residue charge

Let alpha be a formal parameter near 1. Define F_0(alpha)=1 and

 F_(k+1)(alpha)/F_k(alpha)
   =u(q^L-alpha^d q^k)/(1-alpha^d q^(k+1)).

The displayed fraction defines F_(k+1) by multiplication, rather than requiring division by F_k. All denominator factors have unit constant term at alpha=1. Hence F_k is a well-defined formal series, F_k(1)=f_k. For every rational p for which substitution makes sense, direct cancellation of interior terms gives

 sum_(k=0)^L F_k(alpha) T(p)(alpha gamma^k)
  =(1-alpha^d)p(alpha/gamma)
    +u q^L(alpha^d-1)F_L(alpha)p(alpha gamma^L).       (A)

This is an identity of rational functions of alpha. It uses no claim T(p)=E away from the finite grid.

Over either actual hidden field, suppose T(p) is regular at every sampled point and takes the prescribed values E(gamma^k), while p has at most simple poles at the two external boundary points gamma^(-1),gamma^L. Taking alpha->1 in (A) gives

 S=-d gamma Res_(x=gamma^-1)(p)
   +d u gamma^((d-1)L) f_L Res_(x=gamma^L)(p).        (B)

Indeed p(alpha/gamma) has principal term gamma*Res/(alpha-1), whereas p(alpha gamma^L) has principal term gamma^(-L)*Res/(alpha-1). Higher-order poles or interior poles are not automatically disallowed; when regularity of T(p) makes (A) finite, its finite part must include the required higher jets and cancellations. Equation (B) only asserts the simple-boundary-pole case.

Thus a finite-grid rational object with cancelled boundary poles is a genuine escape from the zero-compatibility matrix. It is not licensed to set these boundary contributions to zero. If one residue is fixed as zero, the other is the query times a known unit. More generally their weighted combination is exactly the query. This is a conservation identity, not a computational lower bound or a proof that the residues cannot be acquired cheaply.

The statement is local in either hidden field. A composite implementation needs denominators with a valid factor-aware interpretation and local expansions at the prescribed unit points. Formal cancellation of a polynomial denominator that becomes identically zero in one hidden field is not such an interpretation.

## 4. A concrete operator deformation exposes the same missing coefficient

Keep a_k fixed and replace b_k by

 b_k(epsilon)=-u((1+epsilon)q^L-q^k).

Solve equations 0,...,L over R((epsilon)), with the new unknown p_L included. The first L diagonal entries have unit constant terms, while b_L=-u q^L epsilon. Let f_0(epsilon)=1 and

 f_(k+1)(epsilon)
  =u((1+epsilon)q^L-q^k)/(1-q^(k+1))*f_k(epsilon).

The triangular system has a unique solution with p_0,...,p_(L-1) regular and p_L having at most a simple pole. Telescoping gives

 sum_(k=0)^L f_k(epsilon)E_k
   =-u q^L epsilon f_L(epsilon)p_L(epsilon).

Therefore

 [epsilon^-1]p_L(epsilon)=-S/(u q^L f_L).             (C)

On the actual formal weighted source this pole coefficient is nonzero in both hidden fields. Discarding it when taking a finite part loses the requested sum. Equation (C) does not exclude an efficient algorithm computing that Laurent coefficient; it identifies precisely what the deformation must acquire rather than infer for free from the sparsity of its singular diagonal.

## 5. Positive primitive: selected fixed-order jets are already nearlinear

The previously proved selected-term algorithm extends to both streams above. More generally take

 U_k(epsilon)=product_(r<k)(A(epsilon)-B(epsilon)q^r),
 V_k(epsilon)=product_(r<k)(C(epsilon)-D(epsilon)q^r),

where the four coefficients are supplied in R[epsilon]/(epsilon^(h+1)), their construction is charged, and every requested V_k has unit constant term. Given nu indices 0<=k<=L, the shared block/prefix algorithm evaluates all selected U_k,V_k in soft O(sqrt L+nu) operations in this truncated coefficient ring. It builds degree-b block polynomials, evaluates the complete coarse blocks, then refines all requested endpoints together by monic remainder trees. No node-difference inversions are needed, even with repeated points. Batch inversion of V_k is valid because their constant terms are units.

This directly covers F_k(1+epsilon) in (A), and f_k(epsilon) in (C), without unknown local orders or discrete logarithms. Forming (1+epsilon)^d costs O(log(d+1)) truncated-ring multiplications, or its paid truncated powering cost. At precision h, truncated multiplication costs soft O((h+1)log N) bits by integer polynomial encoding; hence the total bit bound is

 soft O((h+1)(sqrt L+nu)log N),

plus supplied-parameter construction and O(log(d+1)) such multiplications. Storage is soft O((h+1)(sqrt L+nu)) residues. Unit inversion may be done by one constant-term extended gcd and truncated-series inversion after batching. A proper gcd returns a factor; gcd=N is not an inverse. The claimed bound is conditional on the stated unit promise, which the actual retained family satisfies.

For nu=O(m), L=Theta(m^2), and h=polylog(m), the selected-jet part is soft O(m) with the corresponding log N bit factor. A bounded-jet endpoint formula using only such indices and cheaply acquired residue coefficients would therefore have its coefficient-stream evaluation paid. The missing part is constructing that formula and its residue coefficients: (B) and (C) show why identifying a singular boundary is not itself acquisition of its weighted residue.

## 6. Provenance and outcome

The finite matrix, moving-grid identity (A), boundary formula (B), and deformation formula (C) are proved above by direct algebra. No characteristic-zero q-Hermite, analytic finite-part, or root-of-unity interpolation theorem is imported. The jet algorithm is the existing selected-coefficient block algorithm over a new coefficient ring; its exact prerequisite report is pinned in manifest.json. The actual-order/density premises and native source pins are also recorded there.

This closes only the specific proposals to obtain an endpoint formula by ignoring the finite-grid compatibility defect, dropping a boundary residue, or discarding the singular coefficient of the displayed deformation. It leaves an efficient computation of those residues/defects, more general regularization, several streams, weighted combinations, and direct norm methods open. No soft O(m) actual-source query or improved factoring exponent is claimed.
