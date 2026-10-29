# Reciprocal adjacent-pair scalar: exact Links–Gould identification and failed universal zero implication

26 October 2026. Primary-source and exact symbolic audit; no numerical sampling or repository edits.

**Outcome.** The reciprocal GK n=1 candidate is the first V_1/Links–Gould invariant, with an exact variable dictionary. Its normalized scalar does **not** universally preserve Alexander-product zeros. The figure-eight knot gives a symbolic counterexample with resultant 25; all field components of characteristic other than 5 satisfying its Alexander-root relation instead have nonzero coupled scalar. This is an arbitrary-knot diagnostic, not a certified attained member of the full native Seifert catalogue family. A special native realization would still need its own proof or counterexample.

## 1. Proved identification and exact native dictionary

Garoufalidis–Harper–Kashaev–Kohli–Wagner, arXiv:2509.10911v3 (17 December 2025), introduction following Conjecture 1.4, records that its n=1 case was proved by the common uniquely determining skein theory of Garoufalidis–Harper–Kashaev–Kohli–Song–Tahar, *Skein theory for the Links–Gould polynomial*. Its equations (10),(13) give

    LG^(1)(Q^alpha,Q)=V_1(Q^(2alpha+1),Q²),
    (t_0,t_1)=(Q^(2alpha),Q^(-2alpha-2))
             =(t*tildeq^(-1/2),t^-1*tildeq^(-1/2)).       (1)

Here Q is the representation-theoretic quantum parameter and tildeq is the GK Nichols parameter. Neither should be silently identified with its own square.

For the supplied reciprocal pair use

    tildeq=q=eta²,  t=eta^(-2i-2),  Q=eta.

Then (t_0,t_1)=(eta^(-2i-3),eta^(2i+1)), exactly the desired independent parameters in the reverse order. The LG invariant is symmetric in t_0,t_1. Thus the candidate scalar is

    C_i(K)=LG_K(eta^(2i+1),eta^(-2i-3))
          =V_1,K(eta^(-2i-2),eta²).                    (2)

The normalization is unknot=1 and split-link=0 (skein paper Lemma 3.2); this is a normalized Laurent polynomial, not a generic modified-dimension quotient evaluated after division at a collision. The cited proof identifies the polynomial invariants; it does not automatically certify a singular specialized full matrix representation or every rotated inverse in R. Evaluating the polynomial identity itself over R is legal.

Sources: https://arxiv.org/html/2509.10911 (v3, Eq.10, Eq.13); https://arxiv.org/html/2505.19251 (Theorem 1.1, Lemma 3.2 and Appendix A); published skein paper DOI https://doi.org/10.1112/jlms.70522 .

## 2. Explicit scalar on the figure-eight knot

David De Wit, *An Infinite Suite of Links–Gould Invariants*, arXiv:math/0004170v3, Section 4.1 defines P=q_old^(2alpha+1) for gl(2|1), and Section 4.3 prints the rank-two Links–Gould polynomial of 4_1:

    LG^2_(4_1)(P,q_old)
      =P²+P^-²-3(q_old+q_old^-1)(P+P^-1)
         +2(q_old²+q_old^-²)+7.                       (3)

The later paper reverses the representation variable convention; (3) is symmetric under P inversion and q_old inversion, so that distinction does not change this formula. With P=t and q_old=eta (or their inverses), it gives

    V_1,4_1(t,eta²)
      =t²+t^-²-3(eta+eta^-1)(t+t^-1)
         +2(eta²+eta^-²)+7.                           (4)

As a normalization check, eta=1 gives (t+t^-1-3)²=K_4_1(t)², since K_4_1(T)=3-T-T^-1 and K_4_1(1)=1. This check alone is not the source of (4); the full polynomial is supplied by the primary table and dictionary.

Source https://arxiv.org/pdf/math/0004170 , Section 4.1 and Section 4.3 (PDF pp.11–13). The arXiv cover metadata reads v3, 9 July 2000; the compiled PDF front page also displays 24 October 2018. Both are recorded rather than treating the compilation date as a new theorem version.

## 3. Exact symbolic collision certificate

Set i=1. The target pair is K_4_1(eta³)K_4_1(eta⁵), while its candidate scalar is V_1,4_1(eta^-4,eta²). Work over a commutative ring where eta is a unit. The first Alexander factor vanishes when

    f(eta)=eta⁶-3eta³+1=0.                             (5)

Multiplying the coupled scalar by the unit eta⁸ gives the integer polynomial

    g(eta)=eta¹⁶-3eta¹³-3eta¹¹+2eta¹⁰+7eta⁸
             +2eta⁶-3eta⁵-3eta³+1.

Exact monic division gives

    g mod f = r=-6eta⁵+8eta⁴+3eta³+2eta²-3eta-1.

The exact integer Sylvester resultant is

    Res_eta(f,r)=25.                                  (6)

Thus f and r have no common root over characteristic zero or any field of characteristic other than 5. More strongly their integral Bezout resultant identity shows that r, and hence the coupled scalar, is a unit in any coefficient ring with f=0 and 5 invertible. The desired Alexander pair product is zero in that same ring. This refutes the universal implication

    K(t_1)K(t_2)=0  ==>  C_i(K)=0

for the particular lawfully coupled scalar, without numerical knot evaluation. The needed inverse-free symbolic calculations were monic polynomial remainder and an integer Bareiss determinant of the Sylvester matrix; a reproducible exact script is retained alongside this report.

This does not rely on a short-order clock: take the positive real eta=((3+sqrt(5))/2)^(1/3)>1. It satisfies f=0 and has infinite multiplicative order, as does eta². Therefore abstract large/infinite-order margins do not restore the proposed universal scalar identity. In finite characteristic, equation (6) similarly proves the conditional statement at every admissible f-root away from 5, but it does not by itself supply a prime/root meeting the entire native growing-order and catalogue contract.

## 4. Scope for the actual native knot and the next constructive route

The counterexample uses the figure-eight knot, whose Seifert genus is one. It is NOT a claim that the full native acquired degree-2L K equals that Alexander polynomial, or that a native catalogue label achieves equation (5), or that an integer-lift native realization contains this knot as a connected-sum summand. In particular a claim about the actual chosen native knot requires its specified topology: Seifert matrices and Alexander polynomials alone do not determine the full Links–Gould invariant.

What is now excluded is the proposed universal collision-preserving replacement of each adjacent Alexander pair by its n=1 GK/LG scalar, justified merely by reciprocity, resonance and order margins. The small module exists; its exact normalized scalar has the wrong zero predicate already for an explicit ordinary knot. A native-specific bridge would need extra structure and must be proved independently.

The acquisition refinement suggested during this audit is now supplied by [twist-lift.md](twist-lift.md). Kohli's *The Links–Gould invariant as a classical generalization of the Alexander polynomial?*, Proposition 2.18 and connected-sum Proposition 2.5, give the needed formulas: https://arxiv.org/pdf/2505.08296 . Choosing the native knot as the specified connected sum of negative, binary-encoded twist knots acquires its complete fixed-u coefficient polynomial in soft O(L), without expanding a diagram. This construction retains the integer twist lift, source convention and all removable denominators. The native collision-preserving bridge and fast whole-family contraction remain open; the universal argument above cannot supply them. No product-query exponent gain is proved here.
