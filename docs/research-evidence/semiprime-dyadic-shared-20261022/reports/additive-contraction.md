# Shared additive contraction: truncation-first state audit

22 October 2026. This pass attempts an actual Bostan–Mori/Graeffe contraction of

 H_a=CT[rho_(a/b)(B)R^a], B=W^N, R=W/X,
 W=t(1+gamma X)/(X+gamma), m=2^k, b=N mod m,

for odd a<m in A=(Z/NZ)[X]/(X^m−1). All exponents and cyclic wraps are retained. No soft O(m) constructor was obtained. The audited failure point below is a moving NUMERATOR/state, not the degree of an unneeded full resolvent.

## 1. Exact additive state at one rank-halving step

Set n=m/2,Y=X². Write B=B0(Y)+XB1(Y), R^a=E_a(Y)+XO_a(Y). If c=a/b mod m is represented by an odd integer,

 H_a=CT_Y[B0(Y^c)E_a+Y^((c+1)/2)B1(Y^c)O_a].             (1)

If u=b^-1 mod m and a=2s+1, the phase is EXACTLY

 Y^((c+1)/2)=Y^((u+1)/2)*(Y^u)^s.                       (2)

The quotient carry disappears only because its exponent is a multiple of n. The original integer a in E_a,O_a remains.

With

 r0=t(gamma²−1)/(gamma²−Y),
 r1=t gamma(1−Y)/(Y(gamma²−Y)),
 M=[[r0,Yr1],[r1,r0]],

we have (E_a,O_a)^T=M^a(1,0)^T. Thus the actual odd-output state uses M(M²)^s. M's determinant is Norm_relative(R), not R². The denominators are units under the retained prepared orders.

For the special B, B0,B1 are the two homogeneous coordinates of W^N. Their quadratic norm equals W_(gamma²,gamma)(−Y)^N, but this does not determine either additive coordinate in (1). In fact B0(1)=0 for odd N, so dividing by it would already fail on a public component.

The fixed norm BASES across the dyadic tower cost soft O(m). A canonical reduction a=a0+n*epsilon additionally leaves a vector factor (Norm R)^n raised to epsilon. A correct additive algorithm must share both coefficient parity coordinates AND these exponent bands. Keeping just the norm loses the mixed sum (1).

## 2. Exact prefix representation and the numerator that must be built

Extend the definition to all nonnegative integers a using cyclic substitutions (not requiring that a be a unit). Write B=sum_(j=0)^(m−1) B_j X^j. Over an etale splitting extension, used only for the proof,

 F(z)=sum_(a>=0) H_a z^a
 = (1/m) sum_(omega^m=1) sum_j B_j /
                 (1−z R(omega) omega^(u*j)).           (3)

For omega of exact order d|m, its inner sum equals

 [sum_(r=0)^(d−1) (z R(omega))^r B(omega^(u*r))]
       /[1−(z R(omega))^d].                            (4)

This is an identity of rational functions and formal series. At primitive order d=m, the denominator is 1 modulo z^m. Therefore its contribution to the first m moments depends ONLY on the numerator

 sum_(r<m) z^r R(omega)^r W(omega^(u*r))^N.              (5)

A large full denominator is NOT an obstruction to a near-linear PREFIX algorithm. In particular its primitive part has degree m²/2 before cancellations, and a straightforward full common denominator over all strata has degree sum_(d|m)d*phi(d)=(2m²+1)/3, but neither degree is a lower bound on computing the needed prefix. For odd outputs, pairing opposite poles reduces the full degree further. None of these full-order facts resolves (5).

What is actually unpaid is simultaneous construction/contraction of (5), or of its lower-order-stratum analogues (4), without listing its r-by-omega table. The special B gives its numerator coefficient the structured form W(omega^(u*r))^N; it does not make it a fixed weight independent of r.

## 3. Attempt to feed a truncation-first Graeffe algorithm

Let the orbit kernel be

 P_B(X,v)=sum_(a=0)^(m−1) B(X^(u*a)) v^a.

It has an O(m)-size IMPLICIT description (one B and the rule for substitutions), but its explicit coefficient rectangle has m² positions. Our desired prefix is a Hadamard coupling in the output index a between P_B and the rational series 1/(1−zR(X)); it is NOT their ordinary product. Replacing this Hadamard operation by multiplication would mix B(X^(u*r)) with R^(a−r) and compute different values.

In Kinoshita–Li's supplied power-projection interface, the functional is fixed and the starting numerator is independent of the output variable. Their Graeffe update multiplies numerator by Q(−X,z), selects one X parity, and halves the selected X coefficient. For the present orbit kernel, a shift of a changes B(X^(u*a)) to B(X^(u*(a−1))). On its coefficient B_j this is modulation by X^(−u*j). These j-dependent modulations must remain coupled to the X-parity selection and to the M² power in (1). They are not a scalar adjustment of one fixed functional.

One can keep these operations as a short expression DAG, but evaluating its final scalar contractions is the unresolved operation; DAG size alone is not an arithmetic complexity proof. Conversely, an implementation explicitly retaining a weight vector for every surviving output index has (m/2)*m coefficients already at the top level. Dividing X rank by two does not by itself remove the index-by-weight axis. This is the cost of that PARTICULAR state representation, not a lower bound for other representations.

The concrete sufficient refinement is a data structure for the orbit kernel whose Graeffe numerator update, parity extraction, and exponent-band correction can each be performed with TOTAL soft O(m) work across all levels. Such a structure must preserve the exact two terms of (1); the fixed-weight resolvent theorem supplies no such update automatically.

## 4. A separate exact q-difference candidate for the special Nth power

For a fixed cyclic root omega, set q=omega^u and z0=q^a. Its scalar summand T_a(omega)=W(q^a)^N R(omega)^a obeys

 T_(a+1)(omega)/T_a(omega)
 = R(omega) * [(1+gamma*q*z0)(z0+gamma)
              /((1+gamma*z0)(q*z0+gamma))]^N.          (6)

All factors represent actual cyclic units; the identity does not replace gamma by q. This gives a genuine first-order q-difference equation and uses the special Nth power explicitly.

However its rational coefficient has numerator/denominator degree 2N before cyclic reduction in z0. It can be stored as an exponentiation circuit of logarithmic depth, but a standard recurrence algorithm charged by explicit polynomial degree cannot treat that as degree two. Reducing modulo z0^m−1 gives acquired degree<m vectors for ONE q, not all omega at scalar cost. A shared circuit-aware q-difference algorithm could be valuable, but its all-root/all-prefix preprocessing and contractions must be proved; neither Bostan–Mori nor the inspected power-series composition theorem provides this model.

No conclusion that high degree forbids a faster algorithm is drawn. Equation (6) is the concrete alternative recurrence whose compressed evaluation would have to be developed. The preceding norm closure does not supply its additive contractions.

## 5. Special characteristic does not justify erasing cyclic aliases

Because the coefficient ring is Z/NZ, the formal derivative of W(X)^N is zero. In its Taylor expansion around X=0, n*[X^n]W^N=0. For 0<n<min(P,Q), n is a unit and those coefficients vanish. This is a legitimate strong formal gap, but its cyclic representative B includes coefficients from ALL indices congruent modulo m, including indices beyond the hidden factors. Replacing B by the constant Taylor prefix therefore loses precisely the wrap information being queried. No step above does so.

## 6. Source-exact conclusion and sources

The paid input consists of O(m) coefficients and soft O(m) preprocessing. We have exact recurrences (1), (3)–(6), with every matrix rank, moving weight, and integer exponent identified. The attempted fixed-numerator Graeffe contraction fails to close at the orbit-kernel numerator update; the attempted scalar q-difference contraction retains a high-degree Nth-power coefficient. I did not obtain the required shared additive evaluator. The full native row also retains its separate carried factor W_j^ell, so solving this power piece alone would still need integration with the original scalar same-leaf recovery contract.

Primary interfaces inspected:

- Kinoshita–Li, *Power Series Composition in Near-Linear Time*, arXiv:2404.05177v2, Definition1 and §3.1/Theorem6, https://arxiv.org/abs/2404.05177. Their input is a fixed linear form w and powers modulo X^n; its numerator/degree invariant is explicit. No cyclic-to-nilpotent replacement is made here.
- Bostan–Mori, *A Simple and Fast Algorithm for Computing the N-th Term of a Linearly Recurrent Sequence*, SOSA2021, https://mathexp.eu/bostan/publications/BoMo21.pdf and https://arxiv.org/abs/2008.08822. Its O(M(d)log N) arithmetic bound assumes supplied rational generating data/order d. It is not a theorem for implicitly orbit-weighted numerators.

No generic-group lower bound, finite success campaign, implementation claim, or factoring-rate improvement is asserted.

## 7. Follow-up: coefficient-index folding FIRST, with the spatial trace fully contracted

This follow-up executes the proposed alternative order rather than assuming it is equivalent to the earlier state. Work first on the primitive order-m component, so X^(m/2)=−1. In equations (8)–(9), CT_X and CT_Y denote NORMALIZED traces on the primitive order-m and order-d components, and H means that normalized primitive contribution. The original cyclic CT is the sum of the order-e normalized contributions weighted by phi(e)/m. Put d=m/2, u=b^-1, v=R(X), q=X^u. Pair coefficient indices k,k+d in the inner resolvent (3):

 sum_(k<m) B_k/(1−z v q^k)
 =sum_(k<d) [(B_k+B_(k+d))+z v q^k(B_k−B_(k+d))]
                /(1−z²v²(q²)^k).                     (7)

For the odd output prefix let Z=z² and C_k=B_k−B_(k+d). Its exact series is

 G(Z)=sum_n H_(2n+1) Z^n
     =CT_X sum_(k<d) C_k R(X)X^(uk)
                         /(1−Z R(X)² Y^(uk)).          (8)

The denominator is 1 modulo the corresponding output precision only when its actual degree/valuation warrants that; no whole cyclic alias is discarded. Define relative trace S=2r0, norm P=R(X)R(−X), A=S²−2P, and s=Z Y^(uk). Taking the spatial trace NOW yields the explicit scalar kernels

 K_even(s,Y)=r0*(1−sP)/(1−sA+s²P²),
 K_odd(s,Y)=Y*r1*(1+sP)/(1−sA+s²P²).

Consequently

 G(Z)=CT_Y sum_(k<d) C_k Y^floor(uk/2)
                               K_(k mod2)(Z Y^(uk),Y). (9)

The factor 1/2 from relative trace is already included in these kernels. Equation (9) is a genuine completed first numerator contraction. It uses only d scalar C coefficients and two constant-degree rational kernels; it does NOT require listing the original m-by-m numerator. All parameters S,P,r0,r1 are acquired in soft O(m). For lower-order cyclotomic strata one first folds B's coefficient indices modulo that order, and uses that stratum's primitive X; their initial coefficient sizes sum soft O(m). Formula (9) applies at each order >=4, with the two scalar strata handled directly.

Here is the next state exactly, making the remaining synchronization issue visible. Split k=2l+epsilon. The coefficient of Z^n in either kernel is a fixed rational-matrix power sequence in n, multiplied by

 Y^(u*l*(2n+1))

and, in the epsilon=1 branch, an additional known Y^(u*n+(u−1)/2) (with the Y*r1 kernel prefactor retained). Thus the tag parameter is 2n+1 while the matrix power parameter is n. They are no longer the same synchronized index. The input coefficient lists C_(2l), C_(2l+1) have length d/2 and together size d.

This does NOT immediately invalidate recursion: an affine-tag state may be the right invariant. But it must be specified and its update paid. Repeating a Bostan–Mori parity extraction in n gives both subseries n=2r and n=2r+1, with tags 4r+1 and 4r+3 and corresponding matrix-square/prefactor changes. Repeating coefficient folding while keeping tag 2n+1 instead does not automatically halve n precision; it retains the old exponent range and therefore its high bands. Neither operation is the one-state fixed-numerator Graeffe recurrence supplied in the cited theorem.

A concrete sufficient invariant would therefore store affine tags alpha*n+beta, the two rational matrix kernels, and the modulated coefficient lists, while ensuring that the TOTAL coefficient/matrix-rank/precision product over all descendants stays soft O(m). The first state (9) meets this target. I did not prove it for the next joint update: sharing the two coefficient lists is straightforward, but sharing both affine output classes with their spatial matrix powers and high bands remains unestablished. Explicitly expanding both sides restores an index-by-spatial-coefficient table. This is an audited failure of the proposed state proof, not a proof that another affine-state representation cannot work.

This follow-up supersedes any interpretation of the full-resolvent degree discussion as a stopping argument: the primitive denominator indeed disappears modulo the requested precision, and (9) computes its first contracted numerator without that denominator. The unresolved object is now the precise affine-tag/matrix-power recurrence after (9).

## 8. Actual new arithmetic acquired during the closure attempt

The subsequent companion report `sheared-norm-constructor.md` proves, with independent review in `sparse-norm-constructor-review.md`, a deterministic soft O(m) constructor for ONE monomial-shift norm denominator. The key support is sheared: at stage p, each z^j coefficient has at most three Y monomials despite a potentially quadratic ordinary rectangle. Known-support sparse multiplication is paid by transposed Vandermonde at the prepared gamma powers, with ALL normalized product exponent differences below 5m²<16m².

Its dual-number addendum also constructs ONE fixed spatial numerator direction U, degree L<=2m, in soft O(m+L). Its tangent support has width 2+L/p, and the corresponding exponent span is below 10m². Thus a fixed numerator's propagation is no longer the unpaid issue; all branch directions must be SUPPLIED/shared before applying that theorem. In the affine folded kernel, the B directions still depend on coefficient-index phases and the output residue. Identifying them with a total soft-O(m)-size family of fixed U directions is not proved. The arithmetic constructor is a positive result, while the full H_a contraction remains open.
