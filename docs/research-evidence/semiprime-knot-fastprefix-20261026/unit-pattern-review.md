# Independent algebraic review: the T(2,4) unit-pattern representation

2026-10-26. Reviewed the construction supplied by the root while `unit-pattern-infection.md` was still being written. **PASS for the explicit representation, Fox calculation, base unit factor, and infection eigenvalue product, with the collision and topological scope qualifications below.** No fast algorithm is established.

## 1. Representation and invariant weight submodule

Take s0=beta^(H/4), which is defined because k=2*3^e and H=k² is divisible by 4. The matrices

    a=diag(s0,s0^-1), b=[[0,1],[-1,0]], c=ab

satisfy b²=c²=-I, and b a b^-1=a^-1. Hence the relator r=a c² a^-1 c^-2 maps to I.

On the monomial basis u^(n-j)v^j of Sym^n, n=2m+1, diagonal a has weights n-2j. The matrix b interchanges the +w and -w monomials with coefficients +/-1. Thus deleting the two basis monomials of weights +/-1 leaves a free invariant rank-2m submodule with weights +/-3,...,+/-(2m+1), invariant under a,b,c. This does not require projection by factorials or binomial denominators. Since Sym^n(-I)=(-1)^n I=-I for odd n, the restricted matrices A,B,C satisfy B²=C²=-I exactly over the composite ring.

Each paired weight block of C has shape [[0,u],[v,0]], with uv=-1. Therefore det(C-I)=1-uv=2 per block, and

    det(C-I)=2^m,
    (C-I)^-1=-(C+I)/2.

All these inverses are legitimate because N is odd.

## 2. Fox derivatives and base acyclicity

For the presentation <a,c | a c² a^-1 c^-2>, treating a,c as independent generators gives

    rho(partial r/partial a)=I-A C² A^-1=2I,
    rho(partial r/partial c)=A(I+C)-(I+C)=(A-I)(I+C).

The Fox identity checks the signs:

    2(A-I)+(A-I)(I+C)(C-I)=0.

Deleting the c-generator column in the standard deficiency-one torsion formula yields, in the convention numerator-Fox-minor divided by det(C-I),

    tau_base=det(2I_(2m))/det(C-I)=2^(2m)/2^m=2^m.

The inverse torsion convention would invert this unit; sign/basis normalization can also multiply by a unit. None changes the zero/nonunit predicate. More importantly, this is not merely a nonzero determinant over one field: C-I and 2I are invertible over R, so the corresponding base chain complex is split acyclic over R. Applying the presentation formula to a topological exterior assumes the standard T(2,4) presentation/spine identification, rather than arbitrary presentation invariance without its simple-homotopy normalization.

## 3. Infection axis and eigenvalues

Use commutator convention [a,b]=aba^-1b^-1. Then

    [a,b]=a²,

in this representation, since conjugation by b inverts a. Thus its eigenvalues on the retained module are

    eta^w, eta^-w,   w=3,5,...,2m+1,
    eta=s0²=beta^(H/2), eta²=q.

If the opposite commutator convention is used, the eigenvalues are inverted; the reciprocal companion K makes the resulting product identical.

The actual controller's local beta-orders are odd. Hence dividing H by powers of 2 does not change the gcd with those orders, and

    ord_p(s0)=ord_p(eta)=ord_p(q)>16H

at both primes. Since 2m+1<=2M+1<ord_p(eta), every eigenvalue minus 1 is a unit modulo N. These facts are essential for the solid-torus/knot-exterior normalization, not merely cosmetic order assumptions.

For the acquired symmetric normalized ordinary Alexander polynomial K, the infection multiplier is

    prod_(w=3,5,...,2m+1) K(eta^w)K(eta^-w)
       = [prod_(i=1..m)K(eta^(2i+1))]^2
       =P_m².

There is no missing eta-power in this equality when K(T)=K(T^-1) is the chosen symmetric Laurent normalization. Combining it with the base convention above gives the cleared determinant expression 2^m P_m², up to the stated unit normalization.

For squarefree N=PQ, this expression is zero iff P_m=0, and nonunit iff P_m is nonunit. Squaring preserves nonunitness in any commutative ring, but zero equivalence needs squarefreeness; it can fail modulo p².

## 4. Topological and collision scope that must remain explicit

The commutator has zero abelianization, so an axis representing it is nullhomologous in the base exterior (zero linking with both base components). It can be represented by an embedded circle and made unknotted in S³ by self-crossing changes in balls disjoint from the base link. Those changes preserve its free homotopy class in the complement, hence the required conjugacy-class representation value and homology. This supplies an existence/encoded-axis construction, not a proved small ordinary diagram bound.

T(2,4) has two components. Infection on a disjoint axis preserves that component count: this construction produces an infected **link exterior**, with a knot K as infection companion. It must not be described as a newly realized single knot without an additional operation and proof.

The base is split acyclic, and the axis-minus-identity matrices are units. The infected complex is **not necessarily acyclic at collisions**. At a prime where K(eta^w)=0, the companion sector has homology; ordinary acyclic Reidemeister torsion at that specialization is then undefined. The expression 2^m P_m² can be used as an extended/cleared determinant or Fitting-type invariant with a separately established infection gluing identity, or as the specialization of a formal identity before collision. Do not claim it is the value of an acyclic torsion defined at every collision. Likewise a field-only infection theorem cannot simply be applied over R at a nonunit determinant without explaining the determinant-level or local-homology extension.

The standard normalization behind the infection multiplier cancels knot-exterior Delta_K(lambda)/(lambda-1) against solid-torus 1/(lambda-1). Here lambda-1 is explicitly a unit, so that cancellation does not erase a collision zero. This reviews the algebra of the multiplier; the exact topological infection theorem/source should be pinned in the construction report.

## 5. Acquisition and algorithmic boundary

The retained representation has dimension 2m. Its paired monomial entries admit compact formulas, and the base torsion 2^m is computable by powering in polylogarithmic work. However explicitly writing all blocks or eigenvalues costs Omega(m), already above soft O(J) when m~k^(3/2). Formula-sized representation data are not a paid acquisition of the full large matrices.

The infection multiplier is exactly the original long odd-stride product, squared. The unit base pattern fixes the earlier problem of a contaminating nonunit base factor, but it does not evaluate that product cheaply. Any new gluing/recurrence algorithm must compute its determinant predicate without expanding those 2m channels and must retain the existing prefix and leaf-recovery contract.

No genuine algebraic sign or norm-prefactor error found. The two genuine scope requirements are that the infected object is a link exterior and that collision specializations use a cleared determinant/homology formulation rather than an assertion of acyclic torsion there. No factoring exponent gain is claimed.

## Final assessment after reading the completed report and reproducer

Read the completed `unit-pattern-infection.md` and `check_unit_pattern.py` on 2026-10-26. **PASS at the report's explicitly conservative scope; no new algebraic/cost error found.** This assessment supersedes the earlier statement that the construction report/source was not yet available.

The completed report correctly separates three levels:

1. The base representation/acyclicity and the finite matrix identity det Z_m=2^m P_m² are unconditional derived statements under the native unit assumptions.
2. Ordinary infection torsion multiplicativity is asserted on the generic acyclic based-field locus, where the companion factors are nonzero. The axis boundary determinants cancel symbolically; their long scalar product is not falsely charged as already acquired.
3. Identification of Z_m with a selected raw infection Fox minor by elementary reductions at singular composite-ring specializations remains an explicit missing chain-level certificate. The report does not claim that certificate has been supplied.

The finite identity (13) requires no raw infection presentation: diagonal G_m decomposes the Kronecker matrix into the matrices V-lambda V^T, each with determinant lambda^L K(lambda). Across reciprocal eigenvalue pairs, prod lambda^L=(det G_m)^L=1, giving exactly P_m². The additional 2I_m block gives 2^m. This proof remains valid at collisions because it is a Laurent-polynomial determinant identity, not because acyclic torsion extends there automatically.

The document now explicitly says the infected object is a genuine two-component satellite link; it also explicitly says its complex may cease to be acyclic at collisions. These address both qualifications in the preliminary review. The phrase “zero-extended determinant/Alexander-order” in Section 4 should be read with Section 5's stated convention: the directly certified singular object is the **chosen determinant representative** (12), with actual raw-minor identification conditional. It must not be cited later as an independently established singular raw Fox/Alexander-order certificate.

The reproducer uses exact standard-library Laurent-polynomial arithmetic. Its Fox implementation treats positive and negative occurrences with the correct prefix rule, and its two relator words match the presentations. The three genus-one companion checks use V=[[c,0],[-1,1]], whose symmetric Alexander polynomial is 1+c(T+T^-1-2), so the asserted squared determinant is the correct expected result. It checks the block algebra and conventions described in the report, not a literal infection diagram/minor or the missing singular reductions. No rerun or additional numerical campaign was performed for this final review.

The expanded order (4L+1)m and O(Lm) nonzero count are correct. The report accurately distinguishes a compact representation descriptor from explicitly acquired rank-2m data and retains the old soft O(L+sqrt(Lm)) query scale. Neither finite identity (13), generic infection interpretation, nor unit base torsion supplies the unpaid fast norm computation.

Editorial resolution by root after this review: Section4 now explicitly states that acyclic torsion is undefined at a collision, and that the polynomial extension is matrix(12); the ambiguous Alexander-order wording was removed. No mathematical claim was broadened.
