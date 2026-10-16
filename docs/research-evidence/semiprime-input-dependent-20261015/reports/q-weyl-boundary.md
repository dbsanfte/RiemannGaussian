# Rank-one q-Weyl defect: exact corrections and a scoped linear-state obstruction

2026-10-15. Independent algebraic investigation of the proposed companion-matrix route. No repository edits. No lower bound for arbitrary scalar algorithms or the special numerical source family is asserted.

## Exact defect and valid prefix range

Let H(X)=X^J+sum_(k<J)h_k X^k be monic over a commutative ring, C its multiplication-by-X companion matrix on the coefficient basis e_0,...,e_(J-1), h=(h_0,...,h_(J-1))^T, and Z the subdiagonal shift. Then C=Z-h e_last^T. Let D=diag(1,q,...,q^(J-1)) and

    v=(q^J I-D)h.

The proposed identity is correct:

    D C-q C D = v e_last^T.                   (1)

Indeed DZ=qZD and e_last^T D=q^(J-1)e_last^T. This is a polynomial, division-free rank-one defect identity. Put T=(I-C)D and P_n(X)=prod_(0<=i<n)(1-q^i X). Then

    T^n e_0 = P_n(C)e_0,  0<=n<=J.            (2)

Before the final step in this range the polynomial has degree<J, so scaling its canonical representative is the true polynomial scaling. This includes n=J, where multiplication first reduces the new degree-J term.

## Exact boundary correction

Write the genuine polynomial division

    P_n(X)=H(X) a_n(X)+r_n(X),  deg r_n<J.

The coefficient vector of r_n is P_n(C)e_0. From P_(n+1)(X)=(1-X)P_n(qX) one gets

    r_(n+1) = T r_n
              + (I-C) rem_H[H(qX) a_n(qX)].  (3)

Here vectors and degree<J polynomials are identified. The formula is exact and requires no inversions. The omitted term depends on the quotient a_n, whose degree is at most n-J once n>=J (with equality when q is a unit over a nonzero ring). Simply declaring the commutator rank one does not determine this term from r_n. Conversely its growing degree by itself is not a universal lower bound: an algorithm may retain or evaluate it implicitly.

The first discrepancy is explicit. The leading coefficient of P_J is c=(-1)^J q^(J(J-1)/2), so a_J=c. Since rem_H H(qX) has coefficient vector -v,

    r_(J+1)-T r_J = -c (I-C)v.                (4)

This is generically nonzero. For J=1, H=X-a, T=1-a; the true P_2(a) differs from T² by a(1-a)(1-q). Thus the rank-one correction is already essential in the smallest quotient.

The direct n-dependent recurrence remains valid with J-dimensional state:

    r_(n+1)=(I-q^n C)r_n.                     (5)

This is precisely the matrix/algebra q-factorial, not a constant-matrix power. Evaluating it by known q-factorial methods over the J-dimensional quotient does not give the target for free; quotient multiplication costs must be paid.

## Why a constant O(J)-state resolvent closure cannot be generic

There is a sharp obstruction to replacing all corrections by one finite-dimensional **constant linear** state over rational-function parameters. It is stronger than a mere count of quotient coefficients, but has a narrow scope.

Let K=Q(a,q), with a,q algebraically independent. Put u_n=prod_(i<n)(1-a q^i). There is no nonzero constant-coefficient order-r recurrence

    sum_(k=0)^r b_k u_(n+k)=0,  b_k in K,

valid even for just n=0,...,r.

Proof. Every u_n is nonzero in K. Dividing by u_n gives

    R(q^n)=0,
    R(z)=sum_(k=0)^r b_k prod_(t<k)(1-a q^t z).

R has degree at most r. The r+1 values 1,q,...,q^r are distinct in K, so R=0. The displayed product polynomials have distinct degrees k and nonzero leading coefficients; they are a basis of K[z]_(<=r). Hence every b_k=0, contradiction.

Consequently any constant s×s matrix B over K and fixed input/output vectors that realize u_n for every 0<=n<=L require s>L/2: Cayley–Hamilton would otherwise give a nonzero order-s recurrence over n=0,...,s. The same applies to a rational generating-function/resolvent realization of bounded state dimension. It applies already at J=1. The matrix and vectors may depend rationally on a,q and on a fixed L; the argument still applies if the realization claims all those prefixes.

This excludes a universal fixed-size constant-matrix-power closure of the rank-one boundary correction that reproduces every prefix. It does NOT exclude:

* the n-dependent recurrence (5), nonlinear state, or compressed q-hypergeometric evaluation;
* an algorithm constructed only to output one horizon without realizing all prefixes;
* a moving-carrier construction with a proved low aggregate cost;
* identities specific to finite numerical q, roots of unity, or the actual semiprime gamma-power source;
* a scalar determinant identity with additional independently acquired data.

In finite fields q has finite order, so the generic rational-function argument cannot simply be transplanted. The retained actual source has extra numerical and arithmetic relations. A positive method exploiting them remains possible and needs its own exact acquisition proof.

## Determinants do not repair the missing correction

Since T=(I-C)D,

    det(T^L) = H(1)^L q^(L J(J-1)/2).

The desired norm is instead

    det P_L(C)=prod_(i<L) det(I-q^i C).

They are different even for J=1. A determinant-lemma expansion of the correction still needs the actual correction data or an exact independent identity; rank one per commutation is not a proof that the total unknown correction is one scalar.

## Outcome

The proposed q-Weyl defect is exact, and equations (3)–(4) locate its missing boundary term precisely. Constant-size generic rational-resolvent closure is impossible if it must realize all prefixes; this is not an obstruction to every intended implicit evaluator. The open positive target is a cheap horizon-specific or n-dependent treatment of these corrections, or a source-specific identity reducing their norm without first acquiring the full q-factorial state.
