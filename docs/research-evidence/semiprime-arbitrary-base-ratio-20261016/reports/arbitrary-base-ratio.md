# An arbitrary geometric base cannot hide the chirped ratio's short mixed alias

2026-10-16. A self-contained finite-sample theorem and a paid factor-or-certificate composition. It extends the previously audited g-base and q-base first-order tests to every advised scalar base h. It is not a general algorithm lower bound or an acquired long query.

## 1. Generic finite-sample theorem

Let K be a field and let g,q,h,Q be nonzero elements. Let D>=0 and L>=1 be integers. Assume

 qQ!=1,       ord(q)>2D+2,       L>=4D+4.                           (1)

The order inequality includes infinite order. Suppose U,V in K[X] have degrees at most D, V(1)!=0, and satisfy the cleared sample equations

 g^k(1-q^(k+1)) U(h^k)+(q^k-Q)V(h^k)=0,
                       0<=k<L.                                   (2)

Then there are integers a,b with |a|,|b|<=D such that

 g=h^a,       q=h^b.                                               (3)

In particular a!=0 if g!=1, and b!=0 since (1) implies q!=1. Consequently g^b=q^a. The coefficients, h and all parameters may be fully advised. There is no independence assumption on g,q,h and no prime-order or characteristic-zero assumption.

For the application where (2) describes the ratio (Q-q^k)/(g^k(1-q^(k+1))), additionally require its denominators and V(h^k) nonzero on the sample range. The theorem itself needs only the cleared equations and V(1)!=0. Those extra regularity assumptions are therefore not hidden in the proof.

## 2. Group the exponential frequencies

Write U(X)=sum_(u=0)^D U_u X^u and V(X)=sum_(v=0)^D V_v X^v. Expanding (2) gives

 sum_u U_u (g h^u)^k-q sum_u U_u(gq h^u)^k
       +sum_v V_v(q h^v)^k-Q sum_v V_v(h^v)^k=0.                   (4)

There are at most4D+4 distinct nonzero numerical bases. Group all equal bases before applying Vandermonde. The first as many consecutive equations as distinct bases exist, and their Vandermonde matrix over K is invertible. Hence every grouped coefficient sum in (4) is zero. Zero coefficients and repeated h-powers do not create an exception.

For each x in K^*, define the finitely supported combined coefficients

 A_x=sum_(u:g h^u=x) U_u,
 B_x=sum_(v:h^v=x) V_v.

The grouped conclusion is exactly the vertex-balance equation

 A_x-Q B_x-q A_(x/q)+B_(x/q)=0 for every x in K^*.                  (5)

Let S={x:A_x!=0 or B_x!=0}. Then |S|<=2D+2. Moreover S is nonempty: sum_x B_x=V(1)!=0. Thus the possible cancellation of several polynomial coefficients at the same group element has already been handled, rather than excluded by a distinctness assumption.

## 3. A first active start and its successor

Multiplication by q permutes K^*. Since S is finite, nonempty and |S|<ord(q), some x in S has x/q not in S. Indeed, if every active point had an active predecessor, injectivity on the finite set would give qS=S. Every q-orbit contained in S would then have length ord(q), impossible if that order is finite and greater than |S|, and also impossible if its order is infinite.

At such an x, equation(5) becomes

 A_x=Q B_x.

Both combined coefficients are nonzero: Q is a unit and x is active. Hence some u_0,v_0 in [0,D] occur with g h^(u_0)=x=h^(v_0). Therefore

 g=h^a,       a=v_0-u_0,       |a|<=D.                              (6)

The successor qx MUST be active. Otherwise (5) at qx, where its own A and B are zero, gives

 0=-q A_x+B_x=(1-qQ)B_x,

contrary to (1) and B_x!=0. If A_(qx)!=0, choose u_1 in [0,D] with g h^(u_1)=qx and compare with the already existing U-side index u_0 at x. This gives q=h^(u_1-u_0). If instead B_(qx)!=0, choose v_1 in [0,D] and compare with v_0, giving q=h^(v_1-v_0). In either case q=h^b with |b|<=D. This proves (3). The selected original indices exist because their combined sums are nonzero. No assumption about uniqueness of those indices is made.

This argument can be pictured as two types of q-directed edges: a U edge starts at g h^u, with endpoint coefficients U_u and -qU_u; a V edge starts at h^v, with endpoint coefficients -QV_v and V_v. The proof uses grouped coefficients and a missing predecessor, not division by a potentially zero-divisor element of a finite group algebra.

## 4. Chirped finite q-binomial ratios

Let d=m², q=g^d, L=2d+2, m>=3. Define

 F(T)=product_(i=0)^(L-1)(1-q^i T)=sum_(k=0)^L c_k T^k,
 A_k=c_k g^(-binom(k,2)).

Assume the local q order exceeds16m², as in the paid prepared base or the original qualified prime-order source. All these coefficients are nonzero, and the exact ratio is

 A_(k+1)/A_k=(q^L-q^k)/(g^k(1-q^(k+1))), 0<=k<L.                  (7)

Suppose arbitrary h in K^* and arbitrary advised U,V of degrees<=D<=m describe every ratio as U(h^k)/V(h^k), with V(h^k)!=0 on the entire range. The generic theorem applies with Q=q^L: qQ=q^(L+1)!=1, ord(q)>2D+2, and L=2m²+2>=4m+4 for m>=3. It follows that g=h^a,q=h^b with |a|,|b|<=D. Since the local g and q orders exceed16m², neither is1, so a,b are nonzero. Thus

 g^(d a-b)=1,       0<|a|,|b|<=m.                                  (8)

The ratio need not be a genuine rational function of a formal independent base; the conclusion already follows from its finite numerical samples. This covers h with small order, repeated sample nodes, all scalar cosets, and fully input-dependent choices.

## 5. Paid uniform factor-or-obstruction application

The latest all-semiprime setup, at soft O(m) bit cost, either factors the supplied semiprime or supplies beta with both odd local beta orders>16m², coprime local orders, global order>256m⁴, and both local q=beta^(m²) orders>16m². The orders may be composite and are not supplied numerically. Apply the previously proved soft-O(m) square-alias screen: it either factors or certifies beta^(d s)-beta^t is a unit modulo N for 1<=s<=m and 0<|t|<=m. The old screen's proof uses precisely these setup outputs; the latest setup removes its former balance hypothesis without changing the screen arithmetic.

On that certified no-factor branch, (8) contradicts the screen in either hidden field: if a<0 reverse the signs of a,b so s=|a| is positive; then t has nonzero magnitude<=m. Consequently in BOTH fields, simultaneously for EVERY h and advised U,V, no degree-at-most-m regular first-order rational description of all ratios exists.

The scalar h is not required to lift to a known global unit. The claim is stronger and fieldwise: even a private field-specific advised base cannot give the forbidden representation. No enumeration of h or inverse discrete logarithm is performed. The paid cost is only setup and square-alias certification, with ordinary logarithmic residue-bit factors included. No field factorization, hidden order or table of m² pairwise differences is acquired.

On the original qualified prime-order source the generic structural theorem also applies, but an exclusion conclusion requires a separate nonalias hypothesis. The present uniform exclusion uses its explicitly acquired screen; it does not silently replace the literal original base or assume that all original source inputs already avoid every square alias.

## 6. Provenance and exact remaining scope

Finite q-binomial ratios, the chirp, Vandermonde invertibility, monic product/remainder trees, gcd localization and the paid setup/screen are inherited. Prior g-base and q-base reports did not cover arbitrary h. The new step is the grouped q-directed cancellation argument forcing bounded exponents in a common base, followed by the paid short-mixed-alias exclusion. A scoped repository check of the earlier recurrence/source reports found no arbitrary-base version; this is not an absolute literature-priority assertion.

The conclusion excludes this first-order rational-ratio representation on the COMPLETE finite coefficient segment for every scalar geometric base. It does not exclude higher-order recurrences in another base, multivariate/two-clock recurrences, sparse high-degree rational functions, another transformed stream, selected convolution, nonlinear state, direct scalar norm or factor/witness acquisition. A rational function matching only selected query values is outside the theorem. Degree is not a general circuit-size or evaluation-cost lower bound. The existing long-query acquisition clock is unchanged; no query algorithm, full factoring exponent, native edit, Lean declaration, numerical example or broad build is claimed.
