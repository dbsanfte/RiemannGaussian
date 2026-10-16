# Arbitrary-clock recurrences cannot compress the actual private unit-row prefix

2026-10-16. A classical finite-prefix representation theorem for the DIRECT collision product, not the auxiliary chirped coefficient stream. The private unit-row restriction is proof-side and is not acquired by an algorithm. No operation lower bound, query evaluator or all-input extension follows.

## 1. Generic field theorem

Let K be a field of characteristic zero or p, let beta have PRIME order R, and let q=beta^d also have order R. Let A(X) be degree J>=1 with distinct nonzero roots w_1,...,w_J in one coset c<beta>. Set U_0=1 and U_n=product_(i=0)^(n-1) A(q^i). Assume U_n!=0 for every0<=n<=L.

Take nominal order r>=1 and coefficient degree D>=0 with

 D<J,       R>max(Jr,2JrD),
 (Jr+1)(D+1)<=L-r-D+1.                                           (1)

If K has positive characteristic also require p>D. Then no nonvacuous recurrence

 sum_(t=0)^r P_t(h^k)U_(k+t)=0, 0<=k<=L-r, deg P_t<=D              (2)

holds for any nonzero scalar h and advised coefficient polynomials. Nonvacuous means at least one evaluated coefficient FUNCTION on the entire h-orbit is not identically zero. The displayed bounds use the ORIGINAL nominal r even if some coefficient functions vanish identically.

There is also a mixed ordinary-index version. Let P_t(Z,X) have bidegree at most(D_k,D_h), let M=(D_k+1)(D_h+1), and require

 D_h<J,       R>max(Jr,2JrD_h),
 (Jr+1)M<=L-r-M+2,       char(K)=0 or char(K)>max(D_k,D_h).           (3)

Then no recurrence sum_t P_t(k,h^k)U_(k+t)=0 holds throughout the same nominal range if some coefficient function on the nonnegative integer trajectory is nonzero. The geometric-only statement is its D_k=0 specialization. Coefficients, h, roots and initial state may all be privately advised. These are existence obstructions, not algorithms to find a recurrence or the unit restriction.

## 2. A regular sample and exact update polynomials

Prove the mixed statement; write D_h=D. Drop only coefficient FUNCTIONS identically zero on the trajectory. At least one remains. Choose a coefficient function with a first nonzero value at j<=M-1. This bound follows from confluent Vandermonde independence: after grouping repeated h^v, an exponential polynomial sum_v f_v(k)(h^v)^k of polynomial degree<=D_k vanishing at its first M samples has every grouped polynomial zero. Hasse-jet interpolation and the change from falling factorials to ordinary powers prove this when char0 or>D_k; no assumption that characteristic exceeds M is needed. The argument and its finite-characteristic qualifications are inherited from the mixed-clock report.

Replace k by j+k and P_t(Z,X) by P_t(Z+j,h^j X). Bidegrees are unchanged and at least one coefficient has nonzero value at(Z,X)=(0,1). Do not extend the original equation range: at least L-r-j+1>=L-r-M+2 samples remain.

Division by U_(j+k) is legal on the promised unit prefix. Define

 B_t(Q)=product_(i=0)^(t-1) A(q^(j+i)Q),       B_0=1.

It has exact degree Jt. Finite products give

 U_(j+k+t)/U_(j+k)=B_t(q^k).

Thus the shifted equations become sum_t P_t(k+j,h^(k+j))B_t(q^k)=0. Expanding exposes frequencies q^u h^v,0<=u<=Jr,0<=v<=D, each carrying a polynomial in k of degree<=D_k. The bound (3) supplies enough consecutive samples for confluent Vandermonde to force the coefficient POLYNOMIAL in a formal index Z to vanish in EVERY actual numerical frequency group. For D_k=0 this is ordinary Vandermonde. No distinctness of h-powers is assumed.

If the only effective shift is zero, the chosen regular sample already contradicts U_j!=0. The following argument includes lower effective highest shifts without using any extra equations.

## 3. Collinear aliases and formal coarsening

An alias q^a h^b=1 between expanded frequencies has |a|<=Jr and |b|<=D. A nonzero alias cannot have b=0 because ord(q)=R>Jr. For two aliases, eliminating h gives R|(a_1 b_2-a_2 b_1). Its absolute value is at most2JrD<R, so the determinant is zero. All nonzero alias differences are therefore rationally collinear.

If there are no nonzero aliases, grouped coefficient-polynomial vanishing gives the bivariate identity sum_t B_t(Q)P_t(Z+j,h^j H)=0. The polynomials B_t have strictly increasing exact degrees Jt in Q, while their coefficient multipliers are independent of Q. The highest index with nonzero multiplier therefore cannot cancel, contradicting the selected nonzero evaluation.

Otherwise choose the primitive integer direction (a,b) of their rational line, choosing b>0. It need NOT itself be a numerical relation. It satisfies |a|<=Jr,1<=b<=D and gcd(a,b)=1. Substitute formal clocks

 Q=x^b,       H=x^(-a).

Each actual frequency group maps to one Laurent monomial; merging different already-zero groups is harmless. Hence an exact identity over K(Z,x) follows:

 sum_(t=0)^r B_t(x^b) P_t(Z+j,h^j x^(-a))=0.                       (4)

If a=0, the B_t(x^b) have strictly increasing degrees Jtb. All coefficients P_t(Z+j,h^j) lie in K[Z]. The highest nonzero one cannot cancel; thus all would have to vanish. At least one is nonzero by the selected value at Z=0, a contradiction. This handles pure-h aliases and repeated finite-orbit nodes without primitive-lattice saturation.

## 4. Root injection when a is nonzero

Now assume a!=0. Let t_0 be the SMALLEST index for which P_t(Z+j,h^j x^(-a)) is not the zero Laurent polynomial over K(Z). This exists by the selected nonzero coefficient. Since a!=0, substitution into a nonzero polynomial in H is injective over K(Z). Divide (4) by the nonzero B_(t_0)(x^b). Every remaining term with t>t_0 contains the factor

 A(q^(j+t_0)x^b).

Evaluate at its roots. These are Jb DISTINCT nonzero elements in an algebraic closure. Indeed the w_j are distinct and each equation x^b=q^(-j-t_0)w_j has b distinct roots: in positive characteristic, b<=D<p by the characteristic hypothesis, so p does not divide b. In characteristic zero this is automatic.

Their images h^j x^(-a) are also all distinct. If roots x,x' give the same image, put xi=x/x'. Then xi^a=1, while xi^b=w_l/w_(l') is a ratio in <beta>. Therefore (w_l/w_(l'))^a=1. The group has PRIME order R and0<|a|<=Jr<R, so w_l=w_(l'). Thus xi^b=1 as well, and gcd(a,b)=1 implies xi=1. This is where prime local order is genuinely used; a composite-order replacement is not silently allowed.

Consequently the nonzero polynomial P_(t_0)(Z+j,h^j H), regarded as a polynomial in H over K(Z), vanishes at Jb distinct constant arguments. Its degree is at most D<J<=Jb, impossible. This contradiction proves (3) and (1). No unit-prefix cancellation after a zero, or deduction from an uninformative saturated product, is used.

## 5. Actual canonical private restriction

Use the ORIGINAL qualified balanced prime-pair family, with literal projected beta=gamma, d=m²,q=beta^d, prime local orders R_P>P^.677,R_Q>Q^.677, both>16m², and the native canonical length L=2m²+2. This is NOT the newly prepared arbitrary-composite-order beta.

The frozen actual-row-density theorem supplies, simultaneously at every current candidate, m-o(m) labeled canonical rows whose COMPLETE P_L(z_j;q) products are units in Z/N, where z_j=beta^(-N-delta_j), delta_j in[-3m²,m²]. It counts the maximum interval L<=4m², so covers the canonical length. Its extra input deletion O(M^5.992) was already charged against the same original Omega(M⁶/log²M) supply.

Take this private set of unit rows, then deduplicate equal INTEGER offsets. The lowdigit quadratic identity delta_j modm=N(j^(-2)-2j^(-1)) has fibers of size at most2, so at least J=Theta(m) distinct offsets remain. Distinct offsets give distinct z_j in BOTH hidden fields because their difference has absolute value<=4m²<R_P,R_Q. Put

 A(X)=product_j(1-z_j X).

Its roots w_j=z_j^(-1)=beta^(N+delta_j) are distinct and in the same beta-coset (indeed in <beta>). In either hidden field every U_n through L is nonzero: the complete row products are units, so every individual factor1-z_j q^i is a unit. This supplies the EXACT prefix premise required by the theorem. The restriction is not claimed to preserve collision coverage: it deliberately excludes hit rows, and is proof-side rather than an acquired algorithm input.

For any fixed or polylogarithmic r,D_k,D_h, the conditions (3) hold eventually: J=Theta(m), L=Theta(m²), and R>c m^2.031. Also the hidden characteristic exceeds R and hence D_k. Thus the actual direct cumulative product on this private Theta(m)-row unit restriction admits no such nonvacuous arbitrary-clock recurrence. This is a stronger direct-product consequence than merely ruling out a representation of update values.

## 6. Matrix consequence and inherited credit

A rational matrix realization in one geometric clock, or in the pair(k,h^k), can be converted by the PREVIOUS generic cleared-row/minor/interpolation lemma to a nonvacuous scalar recurrence. For dimension s and common numerator/denominator bidegrees(delta_k,delta_h), the coefficient bounds are D_k=s²delta_k,D_h=s²delta_h, with nominal r=s and exactly the original range. The generic scalarization condition char0 or>D_k and this theorem's stronger root-separability condition char0 or>max(D_k,D_h) are both retained. Separate entry denominators and affine augmentation require their previously stated degree/dimension charges. Substituting these bounds into (3) excludes all fixed/polylogarithmic such matrix realizations on this private unit restriction. This conversion is a standard inherited representation argument, not a new fast constructor or an order oracle.

Old G15 already treats U_n=product_i F(theta^i) with SAME-clock polynomial recurrence coefficients, explicitly assuming nonzero prefixes and proving K<=h*deg(F)+delta for delta<deg(F). That is not claimed new. The new application permits an ARBITRARY scalar clock and mixed ordinary-index dependence, uses actual prime-order root-ratio injection, and keeps the zero-free private restriction explicit. Alias coarsening, Vandermonde/Hermite arguments, polynomial root counting and matrix scalarization are inherited techniques.

The full canonical rectangle has forced collisions, so its scalar cumulative product eventually vanishes in at least one field. One must NOT transfer this theorem to arbitrary recurrences of that saturated scalar sequence without a zero-free-prefix argument. The update-value theorem in direct-update-clock.md is a separate statement with no such division. Neither theorem is an arithmetic-operation lower bound, a nearlinear query algorithm, a proof of hard scalar values, or an all-input factorization result. Other representations, genuine multiple geometric clocks, high-degree sparse circuits, selected sums and direct factor/witness methods remain open. No native edit, new Lean declaration, experiment or broad build follows.
