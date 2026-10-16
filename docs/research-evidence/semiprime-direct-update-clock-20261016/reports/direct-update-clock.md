# Every geometric clock needs target-degree rational complexity for the direct update values

2026-10-16. A classical finite-sample representation theorem for the ORIGINAL query's transition multipliers. The old original-norm degree rigidity is credited explicitly. No query acquisition, factoring exponent or general operation lower bound is proved.

## 1. Query orientation and the distinction from a ratio after zeros

For actual targets Y_j=beta^(N+delta_j), write z_j=Y_j^(-1) and define

 A(X)=product_(j=1)^J(1-z_j X),       A(0)=1.

Then product_(i<L)A(q^i) equals the desired product of Y_j-q^i differences times the known unit(product_j Y_j)^(-L). Using product(1-Y_j X) at q^i instead would reverse the seed orientation and is NOT silently substituted here.

Let U_0=1 and U_n=product_(0<=i<n)A(q^i). The exact update is U_(n+1)=A(q^n)U_n. In a hidden field a collision makes subsequent U values zero. Therefore A(q^k) is a well-defined TRANSITION MULTIPLIER even there, but must not be called the numerical ratio U_(k+1)/U_k after U_k=0. The main theorem below concerns those multiplier samples directly. A unit-row restriction giving a legitimate nonzero-prefix ratio is discussed separately in section6.

## 2. Short arcs force primitive coefficient support

Let K have characteristic zero or characteristic p>J. Let beta have finite order R, and let distinct integers delta_1,...,delta_J lie in an interval of width W<R/2. Set z_j=c beta^(-delta_j) for a common c!=0. Assume c lies in <beta> for the actual application; the following scaling argument only needs ratios of the z_j to lie there. Let A(X)=product_j(1-z_j X).

Claim: the gcd of the positive exponents of nonzero coefficients of A is1. For J=1 this is immediate. Otherwise, if that gcd were a>=2, then a<=J and A(X)=B(X^a). Because the characteristic is zero or>J>=a, the a-th roots of unity are distinct. Multiplication by any a-th root zeta permutes A's roots. Some nonidentity zeta exists; since A's roots are z_j^(-1), this zeta is a ratio of two actual roots and belongs to <beta>.

Thus the exponent residue set {-delta_j mod R}, up to a common translate and sign, is invariant under a nontrivial translation of Z/R. If the translating element has order t>=2, any orbit is a coset of the subgroup with t equally spaced residues, spacing R/t. An interval containing the whole orbit on the circle must have length at least R-R/t>=R/2: its complementary gap cannot exceed R/t. Yet every exponent lies in the given integer arc of width W<R/2, a contradiction. This proves the claim. Deduplicating offsets is important: the roots are distinct and J is their actual count.

This is a statement about coefficient support, not coefficient acquisition or its sparsity. The leading coefficient is nonzero, so degree A=J.

## 3. Generic arbitrary-clock theorem

Let K be any field, A in K[X] of exact degree J>=1 with A(0)!=0 and positive nonzero-coefficient support gcd1. Let q be nonzero. Fix D>=0 and L>=1 with

 ord(q)>max(J,2JD),       L>=(J+1)(D+1).                           (1)

The order inequality permits infinite order. Suppose h!=0 and polynomials R_0,S in K[X] of degrees<=D satisfy

 A(q^k) S(h^k)=R_0(h^k),       0<=k<L,       S(1)!=0.               (2)

Then D>=J. In particular a rational description regular on ALL sample nodes must have maximum numerator/denominator degree at least J. The minimum is exactly J, attained by h=q, numerator A and denominator1. The coefficients and h may be fully advised and depend on the entire hidden field/input.

It suffices to prove impossibility when D<J. Write A(X)=sum_(u=0)^J A_u X^u. Expanding (2) gives frequencies q^u h^v with 0<=u<=J,0<=v<=D. Terms from R_0 are in the u=0 row of this SAME frequency grid, not an extra family. There are at most(J+1)(D+1) distinct bases. Consecutive-sample Vandermonde therefore makes each numerical frequency group's coefficient sum zero.

Any nonzero alias difference (a,b) satisfies q^a h^b=1, |a|<=J,|b|<=D. It cannot have b=0, since ord(q)>J. Given two such aliases, eliminate h. The resulting q exponent has absolute value<=2JD<ord(q), so it is zero as an integer. Hence all aliases are rationally collinear. This handles finite orders and torsion without division in a group algebra.

If there is no nonzero alias, formal coefficient comparison in A(Q)S(H)-R_0(H) is zero termwise. Its u=J row would give A_J S=0, impossible because S(1)!=0. If an alias exists, choose a primitive integer direction (a,b) along its rational line, reversing signs so b>0. The primitive direction need NOT itself be a numerical alias. Substitute formal Q=x^b,H=x^(-a). Equal numerical frequencies coarsen to equal formal monomials; merging further groups preserves their already zero sums. Thus

 A(x^b) S(x^(-a))=R_0(x^(-a)) in K[x,x^(-1)].                      (3)

If a=0, this would read A(x^b)S(1)=R_0(1), impossible. Therefore a!=0, and S(x^(-a)) is nonzero. Equation(3) shows A(x^b) belongs to K(x^a).

For completeness, a Laurent polynomial in x belonging to K(x^a) has all its nonzero exponents divisible by |a|. Indeed multiply a representation f(x^a)/g(x^a) by g(x^a) and decompose Laurent polynomials into residue classes modulo |a|. The class-zero product is f; every other class must have zero product with nonzero g, and the Laurent polynomial ring is a domain. Thus |a| divides bu for every exponent u in the support of A. Since gcd(a,b)=1, |a| divides every positive support exponent. Primitivity of A forces |a|=1.

Now H=x^(-a) is either x or x^(-1). Accordingly the reduced rational function in H on the left of (3) is A(H^(+b)) or A(H^(-b)). Its rational degree, meaning max of reduced numerator and denominator degrees, is exactly Jb. In the negative case the denominator is H^(Jb), and A's nonzero leading and constant coefficients prevent cancellation and give numerator degree Jb as well. In the positive case it is a degree-Jb polynomial. Any representation R_0(H)/S(H), reduced or not, therefore has maximum degree at least Jb>=J. This contradicts D<J and proves the theorem. Characteristic or separability assumptions are not needed in this subfield argument.

## 4. Certified actual masks and exact minimum J

Use the paid all-semiprime setup with m an odd auxiliary prime>=5, d=m², L=2m²+2, and q=beta^d. It either factors N or supplies local beta orders>16d and local q orders>16d. Canonical integer offsets lie in[-3d,d]. Deduplicate these offsets publicly. In either field their distinct differences have magnitude<=4d below the beta order, so targets are distinct and differences are units modulo N. The inverse targets z_j above have exponents in an arc of width4d<R/2. Both characteristics exceed16d>J. Section2 proves primitive coefficient support separately in both fields.

For any D<J<=m-1, ord(q)>16d>max(J,2JD), and (J+1)(D+1)<=m(m-1)<L. Thus the arbitrary-clock theorem applies: maximum rational numerator/denominator degree describing the complete transition-value segment A(q^k),0<=k<L, is EXACTLY J in either field. Every advised h, including small-order h and repeated h^k samples, is included. There is NO extra square-alias screening assumption here; only the already paid local order/offset interface is used.

The same argument applies to the ORIGINAL qualified prime-order base gamma, since it also has the required margins. No new exceptional-set deletion is needed for this main theorem. It is about this direct transition sequence, not the earlier auxiliary chirped c_k stream. A row restriction remains a short-arc subset and has the same primitive-support property with its own deduplicated degree.

## 5. Relation to the old original-norm rigidity theorem

The frozen archive object d82b01d0c246795c2483c9316ced7e307d593d09debcfd2cd54d24343ce7c591 (gzip raw and plain hashes in source-pins.json) is titled Finite-prefix degree rigidity for the original long norm, dated2026-10-08. Its Theorem R studies U_n=product_i F(theta^i), coefficients polynomial in the ACTUAL theta^n clock, a nonzero prefix, and degree below deg F. It proves K<=r degF+delta for a putative recurrence. Thus original-query degree rigidity and the growing target-degree issue are already known; this report does NOT claim the first direct whole-query obstruction or the first q-clock result.

The present addition is exact minimum degree J for first-order TRANSITION VALUES in ANY scalar geometric clock, using actual short-arc root geometry to prove primitive support, then alias-line coarsening and rational subfield membership. The old theorem did not quantify over changes to arbitrary h. This is a scoped repository distinction, not an absolute literature-priority claim.

## 6. Optional original-source unit-row restriction: a genuine nonzero prefix

The inherited actual-row-density report concerns the ORIGINAL balanced order-qualified supply P,Q=Theta(M³), current candidate primes m=Theta(M), exact prime local gamma orders>P^.677,Q^.677 and its selector/unit hypotheses. It deletes O(M^5.992) inputs (after the specified previous majority deletions) and retains Omega(M6/log²M) inputs. At each candidate, at least m-1-2M^.997=m-o(m) labelled COMPLETE rows are units in Z/N for every L<=4m². This is an existence/source-count result, not a test or runtime guarantee for every semiprime or for the newly prepared beta.

Choose those unit rows privately as a witness subset. Deduplicate their literal offsets. Each offset occurs for at most two original tags: its low residue c satisfies c j²+2Nj-N=0 modulo m, a nonzero degree-at-most-two polynomial since N is a unit modulo m. Hence this subset has J_unit=Theta(m) distinct targets, still in the same short arc. Unit row products imply that every individual target/seed difference in its entire rectangle is a unit, and so every prefix U_n of this RESTRICTED query is a unit in both fields. There the transition values genuinely equal U_(n+1)/U_n numerically.

Section3 therefore yields exact degree J_unit in every scalar geometric clock for that restricted first-order ratio representation. A restriction-stable sufficient evaluator would have to support such subsets, but the subset is NOT publicly acquired here and no hard-instance oracle or runtime lower bound is inferred. The unit-row-density theorem and its exceptional counts are inherited, not re-proved or extended to the new all-input beta setup. No new loss or balanced-source supply theorem is claimed by this optional consequence.

## 7. Limits and costs

The setup, source target acquisition and the known unit promises are paid as in their pinned report; this theorem adds no acquired long product or rational coefficient data. Vandermonde, short cyclic arcs and polynomial-field residue decomposition are standard tools. The new composition concerns exact advised rational descriptions of one particular transition sequence. It does not exclude higher-order recurrences in another clock, multivariate or nonlinear state, sparse high-degree circuits, selected samples only, selected convolution, early factor discovery, direct norms, alternative witnesses or arbitrary factoring algorithms.

Knowing that a full norm is saturated does not make U_(n+1)/U_n defined after zero; this limitation is why the transition-value and optional unit-subset statements are separated. No operation or circuit lower bound follows merely from the minimum rational degree. The original general query clock remains soft O(J+sqrt(JL)), and the desired restriction-stable soft-O(m) acquisition and complete Lean bit proof remain unpaid. No native edit, new Lean declaration, examples or broad builds are supplied. All earlier files remain immutable.
