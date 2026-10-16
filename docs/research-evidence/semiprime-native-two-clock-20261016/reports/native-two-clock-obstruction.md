# A paid native-clock rectangle excludes bounded-degree direct-query representations

2026-10-16. Classical finite-stream representation theorem. A classical composition for the two RETAINED powers g^k and q^k, with q=g^(m²). They are commensurate, not multiplicatively independent. This closes a specified representation route by certifying a finite nonalias rectangle; it does not acquire the long query or prove an operation lower bound.

## 1. Inputs, direct query and exact scope

Use the paid all-semiprime preparation at public sixth-root scale: N=P Q for distinct odd primes, m>=3, N<=m^6, m=Theta(N^(1/6)), d=m². It returns a factor or a unit g with both odd local g orders>16d, coprime local orders, global order>256m⁴, and both local q=g^d orders>16d. Numerical orders are not supplied. Parity/square preliminary cases are inherited.

For a supplied deduplicated target subset define z_j=g^(-N-delta_j) and

 A(X)=product_(j=1)^J(1-z_j X),       1<=J<=m-1,
 U_n=product_(0<=i<n) A(q^i),       L=2m²+2.

This orientation makes the full product a known-unit multiple of product_(j,i)(g^(N+delta_j)-q^i). A(q^k) is a defined TRANSITION VALUE even when a collision makes U_k zero. Numerical division U_(k+t)/U_k is used below ONLY under an explicit nonzero-prefix promise. No such promise is made for the complete canonical rectangle.

Write Z,G,Q for FORMAL variables corresponding to the ordinary index k and the two running powers g^k,q^k. The symbols g,q in coefficient scalars remain actual field elements. The degree bounds below are separate degrees in these three formal variables. A low formal Q-degree cannot be replaced by a high-degree expression in G without charging that degree: q=g^d is an exact relation, but the screen will exclude its manifestation inside the specified small rectangle.

## 2. Paid rectangle certificate

Choose integer D_g>=0 and T>=0 satisfying

 D_g<d,       dT+D_g<256m⁴.                                       (1)

There is a deterministic procedure of soft O(D_g+1+sqrt((D_g+1)T)) ring operations, with the corresponding residue-bit cost, returning a proper factor or certifying

 g^a q^b!=1 in BOTH hidden fields
 for(a,b)!=(0,0), |a|<=D_g, |b|<=T.                               (2)

Axes b=0 are already certified because local g orders>16d>D_g. For T=0 this finishes immediately. Otherwise build the monic polynomial

 H(X)=product_(-D_g<=a<=D_g)(X-g^a),

including a=0. Acquire its roots by successive powers of g and its known unit inverse, and evaluate H at q^b,1<=b<=T, with ordinary monic product/remainder trees. There is no inversion of point differences and no explicit rectangular array. Compute gcd(H(q^b),N) row by row. A proper gcd returns a factor, and a unit product certifies every difference in that row unit.

A saturated row can be descended through its retained product tree, using gcds of child evaluations. A proper child gcd terminates; a unit child can be discarded; otherwise retain a saturated child. A saturated leaf would give q^b=g^a modulo N, hence a global annihilator

 K=db-a,       0<K<=dT+D_g<256m⁴<ord_N(g).

The lower bound follows from b>=1 and D_g<d. This contradicts the definition of order. Thus a saturated row necessarily produces a proper factor before a saturated leaf. On the no-factor branch ALL tested differences are units. Relations with negative b reduce to these by reversing both exponent signs. This proves (2).

The preceding method is a valid linear-cost implementation, soft O(D_g+T+1). A known generic geometric-product primitive gives the sharper scalar implementation below. This is not a new primitive or a solution to the original long query; the new composition applies it to this much smaller rectangle.

Put h=deg H=2D_g+1. For any supplied contiguous positive b-interval [a,a+t), compute V=product_(b=a)^(a+t-1)H(q^b). For t=0 return1. If t<h use block size s=1. Otherwise set s=max(1,floor(sqrt(t/h))). Build

 P_s(X)=product_(i=0)^(s-1)H(q^i X),       deg P_s=h s,

by divide-and-conquer scaled polynomial products. This costs soft O(hs+h) ring operations: scaling a polynomial argument by a known power of q costs linearly in its degree. For n=floor(t/s) complete blocks, evaluate P_s at q^(a+s j),0<=j<n, using ordinary geometric-progression/chirp evaluation, then multiply the n answers. This evaluation costs soft O(hs+n) ring work, even for unequal polynomial degree and point count. Explicitly, for stride Q0=q^s, the identity Q0^(uv)=Q0^(binom(u+v,2)-binom(u,2)-binom(v,2)) reduces arbitrary-length geometric evaluation to one coefficient convolution after unit diagonal scalings. Only integer powers of the KNOWN UNIT q are used, so repeated nodes are legal and no inverse of1-q^k or point difference is needed. The remaining fewer-than-s tail factors can be evaluated by Horner at cost O(hs); their powers are generated successively. Large initial/stride powers are obtained by modular powering, with logarithmic index costs included. For t<h the h+n bound is O(h); otherwise hs+n=O(h+sqrt(ht)). Thus V is acquired in soft O(h+sqrt(ht)) ring work and that many residue words of storage, up to logarithmic factors.

Take the single gcd(V,N). Gcd1 certifies every rectangle difference unit; a proper gcd factors. If the product is saturated, bisect the b-interval and query child scalar products using the same primitive. A proper child gcd stops, a unit child is discarded and a saturated child retained. At most two child calls per level are needed. The sum of square-root terms along the retained path is O(sqrt(hT)); rebuilding H/setup contributes O(h log(T+1)), absorbed in soft O(h). At the final b-singleton the baby product tree of H localizes a factor, since a globally saturated leaf is impossible by (1). Its sibling-degree sum is O(h). Consequently the complete compressed certificate/factor procedure costs

 soft O(h+sqrt(hT))=soft O(D_g+1+sqrt((D_g+1)T))

ring operations, with corresponding soft O((h+sqrt(hT))log N) bits and softly that many residue words of storage. Trees/block arrays may be discarded between levels. No full b-row array or complete rectangle is materialized. The known generic degree-h/length-T product bound is being used, with all h, block-degree and geometric-evaluation costs retained. Monic arithmetic and the chirp are valid over the composite ring; arbitrary interpolation or quotient-algebra inversions are not licensed.

In particular after the soft-O(m) setup this certificate remains soft-O(m) whenever D_g=soft O(m) and(D_g+1)T=soft O(m²), with logarithmic bit factors understood. Larger rectangles retain their displayed cost rather than receiving a free nearlinear oracle.

## 3. Finite sparse-frequency principle

Fix either hidden field after (2). The elements

 g^v q^u,       0<=v<=D_g, 0<=u<=T,

are pairwise distinct: a collision would give a nonzero relation in exactly box(2). Let D_k>=0 with characteristic zero or>D_k. By confluent Vandermonde, the functions

 k^ell (g^v q^u)^k,       0<=ell<=D_k,

are linearly independent on their first (D_k+1)(D_g+1)(T+1) samples. This follows from Hasse-jet interpolation at the distinct nonzero frequencies and the factorial/falling-factorial basis conversion; only factorials through D_k must be units. The total sample count may exceed the characteristic.

Consequently a polynomial E(Z,G,Q) of multidegree at most(D_k,D_g,T) vanishing at that many consecutive native samples(k,g^k,q^k) is the ZERO FORMAL POLYNOMIAL. This is stronger than numerical vanishing on an unknown short orbit. No initial singularity shift, coefficient-function nonvacuity repair, or finite-orbit interpolation is needed after the rectangle has been certified. A formally nonzero coefficient cannot vanish on all relevant samples under the stated budget.

## 4. Transition-value rational descriptions: no prefix division

Let R_0,S in K[Z,G,Q] each have multidegree at most(D_k,D_g,D_q), with S(k,g^k,q^k)!=0 for every0<=k<L. Suppose

 A(q^k)=R_0(k,g^k,q^k)/S(k,g^k,q^k),       0<=k<L.                 (3)

Take T=J+D_q and assume (1), characteristic0 or>D_k, and

 D_q<J,
 (D_k+1)(D_g+1)(J+D_q+1)<=L.                                      (4)

Cross multiplication gives the sampled zero polynomial E=A(Q)S-R_0 of multidegree at most(D_k,D_g,J+D_q). Section3 makes it identically zero. But S is a nonzero formal polynomial by its regular evaluations; in the domain K[Z,G][Q], deg_Q(A S)=J+deg_Q S>=J, while deg_Q R_0<=D_q<J. This is impossible.

Thus a paid rectangle screen either factors or excludes these rational transition representations in both fields. It applies to the full canonical target set even though its long product has collisions and may be saturated. There is no division by U_k. The result excludes low Q-degree with low retained G/index degrees, not every possible rational presentation: A(Q) itself has the obvious degree J description.

## 5. Nonzero cumulative prefixes: no regular-start loss

Now suppose U_n!=0 for EVERY0<=n<=L in the chosen field. Let nominal r>=1 and polynomials P_0,...,P_r of multidegree at most(D_k,D_g,D_q), not all ZERO FORMAL polynomials, satisfy

 sum_(t=0)^r P_t(k,g^k,q^k)U_(k+t)=0,       0<=k<=L-r.             (5)

No top-coefficient regularity is assumed. Take T=Jr+D_q and require (1), characteristic0 or>D_k, and

 D_q<J,
 (D_k+1)(D_g+1)(Jr+D_q+1)<=L-r+1.                                (6)

Divide only by the promised nonzero U_k and set

 B_t(Q)=product_(i=0)^(t-1)A(q^i Q),       deg B_t=Jt.

The sampled equations give E(Z,G,Q)=sum_t B_t(Q)P_t(Z,G,Q)=0 on the entire ORIGINAL nominal range. Its multidegree is at most(D_k,D_g,Jr+D_q). Section3 forces E=0 formally, with no discarded initial samples and no extension of the original equation interval.

Let t_* be the largest t with P_t nonzero as a formal polynomial. Its term has Q-degree Jt_*+deg_Q P_t*>=Jt_*. All earlier terms have degree at most J(t_*-1)+D_q<Jt_*. Thus the highest term cannot cancel. If t_*=0, B_0 P_0=P_0 is nonzero directly. This contradiction proves the cumulative-prefix statement. It includes smaller effective orders, zero leading evaluations and coefficient functions initially singular; no fictitious extra equations are added.

An evaluated-function nonvacuity assumption, if preferred, implies formal nonzeroness and is therefore also covered. Conversely the certificate and sample budget already rule out a formally nonzero coefficient function vanishing throughout the relevant trajectory segment. This is why the earlier arbitrary-h regular-start shift is unnecessary in the retained native clocks.

## 6. Three-variable rational matrix consequence

Suppose a state v_k in K^s,0<=k<=L, obeys

 v_(k+1)=M(k,g^k,q^k)v_k/B(k,g^k,q^k),       a_k=u^T v_k,

with constant output u, s>=1,L>=s, polynomial M entries and B of multidegree at most(delta_k,delta_g,delta_q), and B nonzero at all actual transitions0<=k<L. Singular M and fully advised state/data are allowed.

Clear s consecutive denominators to form s+1 polynomial rows. In each row every matrix/scalar factor is evaluated at(Z+i,g^i G,q^i Q), so its multidegree remains bounded by the corresponding delta. Each cleared row has multidegree at most(s delta_k,s delta_g,s delta_q). A maximal-rank minor over K(Z,G,Q), followed by Cramer's rule, gives a formally nonzero row dependency with coefficient multidegrees at most

 D_k=s²delta_k,       D_g=s²delta_g,       D_q=s²delta_q.             (7)

Rankzero permits the constant dependency P_0=1. The dependency holds on all row coordinates, not just the selected minor, because the chosen rows span the full rational row space. Its evaluation yields a scalar recurrence of NOMINAL order s over exactly0<=k<=L-s, after dividing only legal window denominators. No invertibility of M or full-orbit regularity of B is assumed.

For a realization of a_k=U_k on a nonzero prefix, apply (5)–(6) with r=s and (7). Whenever the resulting rectangle, characteristic, sample and D_q<J conditions hold, the formally nonzero dependency contradicts section5. There is no finite-orbit interpolation repair or hidden-order input: the paid native frequency certificate itself makes a formal dependency sufficient. All fixed/polylogarithmic s,delta_k,delta_g,delta_q meet these conditions eventually when J=Theta(m),L=Theta(m²).

Separate rational entry denominators require forming/charging a common denominator, with each degree increasing by at most the number of entries times the original entry-degree bound. Affine updates add a constant coordinate and charge its dimension and offset denominators. These are standard representation conversions, not paid acquisition algorithms. The matrix consequence concerns the cumulative U stream under its explicit nonzero-prefix promise; a separate general realization of transition values is not inferred from this scalarization alone.

## 7. Actual applications and source limits

For direct transition values, the all-semiprime prepared base supplies the strong-order interface. With J<=m-1 and fixed/polylogarithmic coefficient degrees, T=J+D_q=soft O(m), D_g<d, dT+D_g<256m⁴, and the sample inequality(4) hold eventually. The compressed rectangle costs soft O(m) bits and either factors or certifies the obstruction. Both hidden characteristics exceed16d>D_k eventually. This is a genuine all-input factor-or-representation-certificate composition for the particular retained native clocks, without assuming local prime orders or a new source exception deletion.

For cumulative prefixes, the FULL canonical rectangle may hit and become zero. Section5 must NOT be applied there without a nonzero-prefix proof. The inherited ORIGINAL qualified prime-order source does supply a private witness subset of m-o(m) labelled unit rows, after its already charged source deletions. Deduplicating offsets loses at most a factor two, giving J=Theta(m) and U_n unit modulo N for all n<=L. On such a private restriction the same rectangle argument applies CONDITIONAL on the screen returning its certificate rather than a factor. The rectangle's global no-saturated-leaf bound is valid for the original gamma as well whenever its actual global order exceeds dT+D_g; that original source supplies an ample order margin for fixed/polylogarithmic parameters.

The companion source-survival-and-novelty.md now verifies an ORIGINAL-source survivor statement. For any fixed polylogarithmic parameter envelope D_g<=polylog M,T<=M polylog M, deleting an additional soft O(M^5.969) ordered prime pairs makes every rectangle difference a unit in both fields, simultaneously over all comparable m. This uses the inherited short-exponent large-prime-divisor count, not a new prime-distribution mechanism. Unioning this loss with the already charged unit-row-density losses retains Omega(M^6/log²M) inputs and their private Theta(m)-row unit restrictions. Thus the prefix obstruction applies on an actual retained original family, not only on a conditional branch that might be empty. The envelope is fixed before input variation; within it coefficients and advice remain arbitrary.

More quantitatively, let r<=M^rho,D_g<=M^gamma,D_k<=M^kappa, with nonnegative fixed exponents, and allow ANY D_q<J. The companion's count gives source loss soft O(M^(5.969+rho+gamma)); rho+gamma<.031 makes it negligible. The recurrence sample count is O(M^(1+rho+gamma+kappa)) up to fixed logarithmic factors, so kappa+rho+gamma<1 supplies the required finite samples eventually. All rectangle size/global-margin conditions also hold in this regime. These are strict inequalities, retaining asymptotic slack for constants and logarithms.

For example, matrix dimension s and every COMMON degree delta_k,delta_g,delta_q bounded by m^.005 give r=s<=m^.005 and D_k,D_g,D_q<=m^.015. The source loss is soft O(M^5.989) and the sample count is O(M^1.035) up to scale constants; D_q<J eventually. Hence this fixed small-power matrix regime is excluded on retained original private unit prefixes as well. Separate entry-denominator degrees must first be converted to common degrees; the example does not omit that cost.

The compressed screen in section2 charges soft O(D_g+1+sqrt((D_g+1)(Jr+D_q))) rather than the linear b-row cost. Thus it remains within soft O(m) whenever D_g<=soft O(m) and(D_g+1)(Jr+D_q)<=soft O(m²). The displayed source-survival power envelope rho+gamma<.031 satisfies this condition with ample slack. In the explicit matrix .005 example its square-root term has exponent(.015+1.005)/2=.510<1, so that certificate is paid within soft O(m) as well. The source-survival statement remains an existence/representation result, not an algorithm acquiring the private subset or the long query. The geometric-product primitive and its general bound are inherited; only this rectangle application is new.

None of this publicly acquires the unit-row subset, asserts unit-row density for the newly prepared all-input beta, or extends the prime-order survivor count to arbitrary semiprimes. A factor from a screen is a useful algorithmic branch; the all-input theorem remains factor-or-certificate. The new original-source survivor composition and its quantitative envelopes are pinned in the companion; the inherited counting mechanism and earlier source losses are credited there.

## 8. Why this is not just old G15

The archived G15 theorem already proves degree/order rigidity for the ORIGINAL cumulative query with coefficients polynomial in its actual q^k clock, on nonzero prefixes. That result is not claimed new. A naive conversion of native-clock coefficients to a single beta clock substitutes Q=G^d and replaces A by A(G^d), whose degree is dJ. Although D_g+dD_q<dJ when D_g<d and D_q<J, the old dense finite-prefix argument would require more than roughly r*dJ samples, unavailable when dJ=Theta(m³) and L=Theta(m²).

The present paid rectangle and sparse native-frequency count instead charge(D_g+1)(Jr+D_q+1), with confluent ordinary-index factors explicit. The highest-Q-degree argument is inherited polynomial rigidity; the new composition certifies the precise finite commensurate-clock range where it can be applied without collapsing Q into a high-degree power of G. Standard monic multipoint arithmetic, gcd localization, Hermite/Vandermonde interpolation and polynomial minors are credited. This is a scoped repository novelty distinction, not a literature-priority claim.

The direct-update and arbitrary-clock reports, unit-row-density source, old G15 archive and all-input setup are pinned prerequisites. This statement does not claim the first direct-query obstruction or a new generic resultant algorithm.

## 9. Exact remaining gap

These are full-segment rational-update and nonzero-prefix scalar/matrix REPRESENTATION statements for ONE ordinary index plus the TWO RETAINED native powers. They do not cover two arbitrary/advised geometric bases, unrestricted multivariate clocks, sparse high-degree circuits, nonlinear state, another stream, selected jump/evaluation algorithms, selected convolution, direct scalar norms, or factor/witness-only acquisition. A high representation degree is not an operation lower bound.

No long product, locator, norm or collision leaf is acquired. The existing soft O(J+sqrt(JL)) query bound is unchanged; the restriction-stable soft-O(m) factor/product/witness query and complete Lean bit-complexity theorem remain open. No native source, frozen report, Lean declaration, numerical example or broad build is modified.
