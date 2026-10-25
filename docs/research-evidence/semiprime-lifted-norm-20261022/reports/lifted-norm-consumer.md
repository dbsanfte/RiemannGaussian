# Cubically lifted native roots: exact batch consumer and missing existence theorem

22 October 2026. The proposed congruence is correct. A complete all-pairs square-relation screen can be constructed in soft O(m), using coprime-base refinement rather than factoring the norm values or trying m² pairs. This is a paid conditional consumer, not a theorem that the native family contains a useful pair. No deterministic all-input soft-m factor/annihilator construction was found. No tests, success examples, heuristics, or repository changes.

## Exact relations and their scale

For the canonical native rows, let Delta=b²-4ac, ell=mb-2aj, kappa=-Delta/(4aj) modm, and v=ell-m²kappa, with the chosen integer representative of kappa. The integer quotient relation implies

    ell²-4aN=m²Delta.

Therefore

    v²-4aN=m²(Delta-2ell*kappa)+m⁴kappa²,

and Delta-2ell*kappa=Delta+4aj*kappa=0 modm. Thus define the exact integer

    M=m³, z=(v²-4aN)/M.

For a≤m and N~m⁶, |v|=O(m³) and |z|=O(m⁴); for bounded a, |z|=O(m³). Every descriptor has O(log N) bits. Modulo N each row gives a genuine square relation

    v²=M z, equivalently (v/m)²=m z modulo N.

This is auxiliary m-adic information, not a square root modulo N of a previously known square with a second distinguished root. The lift depends only on public roots of 4aN modulo m³. It does not by itself approximate aP+Q as a real number. At the true tag, its relation to that trace still contains the unacquired index colour.

Native bounds also keep 0<|v|<N: m does not divide v, the native ell bound gives |v|≤m³+O(m²), and prepared local orders imply P,Q>16m². Hence a gcd(v,N) is either one or already a proper factor. On the no-factor branch every z is nonzero and a unit modulo N. Zero z would imply N|v with the given squarefree semiprime and a coprime to N, contradicting these bounds.

## Paid consumer: screen EVERY two-row square dependency in soft O(m)

Let S be the list of nonzero z values. Acquire a pairwise-coprime integer base B and the exponent factorizations

    |z_j|=product_(b in B) b^(e_jb)

using Bernstein's essentially linear coprime-base algorithm. This is not prime factorization. Its cost is soft in the total bit size O(m log N), and it acquires the exponent representations as well as the base.

Test each b for being an integer square. For each row form a sparse SIGNATURE consisting of its sign and the set of nonsquare base elements b with odd exponent e_jb. Since the base elements are pairwise coprime, two rows have the same signature if and only if their product z_i z_j is a positive integer square. Internal square factors of a nonsquare b cause no problem: an odd power of such a b still has a prime of odd valuation unique to that base element. The total exponent-incidence size is O(sum_j log|z_j|), so sparse signature construction and deterministic sorting cost soft O(m log N). No m-by-m table is generated.

Within one signature class write exactly

    z_j=sigma*D*s_j²,

where sigma is the common sign, D is the product of the signature's nonsquare base elements, and s_j is acquired by exact division and integer square root. D need NOT be squarefree. It and each s_j have O(log N) bits, and all s_j are units modulo N because z_j is a unit. Check those gcds before inversion. Define

    r_j=v_j/s_j modulo N.

Every r_j is a square root of the SAME UNIT M*sigma*D modulo N. Choose one representative r_0 in the class and compute gcd(r_j-r_0,N) and gcd(r_j+r_0,N) for each other member. Return a proper result.

This screens all pairs, not just the representative pairs heuristically. If neither gcd is proper for an r_j, squarefreeness and unit input imply r_j=+r_0 or -r_0 GLOBALLY modulo N. If this happens for every member, any pair is also globally equal up to sign, so no pair in the class can yield a nontrivial congruence-of-squares factor. Conversely if ANY pair is nontrivial, at least one representative comparison must be nontrivial. The number of comparisons is O(m) across all classes.

All construction, integer square tests, divisions, modular inversions, signatures and gcds are soft O(m) in the native bit regime. This is a narrowly useful fully paid consumer for the supplied whole family: it either returns a factor or certifies that no TWO-row square-product relation in that family is useful by this root-comparison mechanism. It does not certify the absence of higher dependencies or of a different use of the lifted roots.

The proof also explains why merely using both Hensel signs is not a guarantee. In the symmetric representative choice v and -v give the SAME z and normalized roots differing only by a global sign; their relation is automatically trivial. More general native representatives must be tested by the consumer, not assumed asymmetric.

## What a higher norm dependency would require

A supplied subset satisfying product_j(m z_j)=Y² gives X=product_j(v_j/m) modulo N, hence X²=Y² modulo N. Constructing X,Y and testing gcd(X±Y,N) is paid in soft(total supplied bit size), using product trees and exact square root. A proper result is sufficient; X=±Y globally is not. The cubic divisibility does not imply the existence of a nontrivial such subset.

Coprime-base exponent parity describes higher square dependencies without factoring the z_j. It does not guarantee a nonzero dependency, nor give a nearlinear general sparse F_2 nullspace algorithm merely from O(m) input rows. A smoothness/factor-base route also needs a rigorous supply of enough appropriate norm relations AND the linear-algebra/recovery cost. The z bounds alone do not provide that supply. None is charged as free or promoted from a smoothness heuristic.

## Primary consumers checked

* Harvey, *An exponent one-fifth algorithm for deterministic integer factorisation*, arXiv:2010.05450, Lemma 3.1 and Lemma 3.3: https://arxiv.org/html/2010.05450 . Its short consumer recovers factors from an ACTUAL trace aq+bp; its coverage lemma supplies rational-approximation multipliers with a real trace error bound. The lifted congruence v²=4aN modm³ supplies neither an actual trace nor that real approximation. Merely knowing a root in a public auxiliary prime-power ring does not satisfy the consumer's input. The old explicit-Lehman-start packet already charges its larger public search volume; it is not rediscovered here.
* Gower–Wagstaff, *Square Form Factorization*, Math. Comp. 77 (2008), 551–588: https://www.cerias.purdue.edu/assets/pdf/bibtex_archive/S0025-5718-07-02010-8.pdf . Their analysis distinguishes useful proper square forms and principal-cycle/inverse-root processing and discusses average multiplier costs. It supplies no guarantee that the present O(m) arbitrary lifted forms contain a proper square form reached within soft m total work. An even representative v produces the primitive indefinite form [m³,v,(v²-4aN)/(4m³)] of discriminant 4aN, but knowing this form is not knowing a useful principal-cycle collision. The discriminant varies with a; nonsquare multiplier changes generally change the field, so rows are not automatically relations in one common class group. Square-related multipliers still require the relevant order/conductor mapping.
* Bernstein, *Factoring into coprimes in essentially linear time*, J. Algorithms 54 (2005), 1–30, author version dated 2004.04.04, document ID f32943f0bb67a9317d4021513f9eee5a: https://cr.yp.to/lineartime/dcba-20040404.pdf ; DOI 10.1016/j.jalgor.2004.04.009. Its explicit coprime-base construction and exponent factorization provide the preprocessing used above; the pair grouping/root-partition consumer is proved here. Fast integer multiplication/division/gcd give the stated soft-linear native bit specialization.

The earlier Carella/common-content and generic Coppersmith independence audits are retained as prior work, not repeated or treated as generic lower bounds. No literature consumer inspected turns this public auxiliary-root family alone into guaranteed all-input small factor information.

## Precise remaining theorem

To close this lead, prove that the explicit native v,z family always contains an actionable pair detected above, or supply another dependency/ambiguous-form/annihilator constructor with fully charged soft O(m) work and nontriviality. The identities and size bounds do not currently prove either. The paid batch pair consumer is available, while universal relation existence remains unproved.
