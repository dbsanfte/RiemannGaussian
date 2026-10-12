# Exact base-squaring q-products cannot use a small invariant algebra

2026-10-08, /root/long_norm_review. Classical route obstruction only.
This note preserves every earlier source, report, manifest and review.
It does not give a new near-linear long scalar evaluator, an arbitrary
scalar lower bound, or the guaranteed sixth-rate factorization algorithm.

## 1. The zero-union query is preserved by the proposed reduction

Let R=Z/NZ, let q be the actual unit alpha=gamma^(m^2), and let
Y_j,u_j be the supplied public units for the actual row targets and their
baby origins. Define the two-parameter finite product

    P_L(X,Q)=prod_(0<=i<L)(1-X*Q^i).

The original residual product has the exact identity

    prod_j prod_(0<=i<L_j)(Y_j-u_j*q^i)
      = prod_j Y_j^L_j * prod_j P_(L_j)(u_j/Y_j,q).       (B1)

Signed public starts are included in u_j. Arbitrary unequal supplied
lengths L_j are retained. The antipodal known-unit normalization merely
changes these origins; it is not used to identify different origins.
Only the known units Y_j are inverted. Individual residuals and norms,
including zero divisors, are never inverted. Thus (B1) retains the original
ANY-zero predicate in each hidden field. It is not the previously rejected
ALL-zero additive Hensel-mask norm.

A natural alternative to dilation at fixed q is the exact even/odd split

    P_(2t)(X,Q)=P_t(X,Q^2)*P_t(X*Q,Q^2),
    P_(2t+1)(X,Q)=P_(2t)(X,Q)*(1-X*Q^(2t)).             (B2)

These are polynomial identities over every commutative ring, with no
division and no root-of-unity hypothesis. A binary recursion changes the
base Q while shifting the origin X.

The specific compression contract considered here keeps a SINGLE finite
free commutative R-algebra A of rank d. Its elements Xbar,Qbar represent
the parameters; the substitution Q->Q^2, X->X must descend to an R-algebra
endomorphism sigma_0 of A. Usually the odd branch also requires a second
endomorphism sigma_1 with Qbar->Qbar^2 and Xbar->Xbar*Qbar. To retain one
actual row evaluation, reduction to either hidden field must admit a
character phi:A tensor_R F_p -> F_p sending Qbar to q modp and Xbar to
the corresponding supplied origin ratio. This is exactly what a quotient
of R[X,Q] with representative-independent substitutions would require.
The theorem below needs only sigma_0 and the Qbar evaluation; adding the
second parameter or more coordinates does not remove its hypothesis.

Here Qbar is an ABSTRACT algebra element whose evaluation is the numerical
alpha; it is not alpha embedded as a ground-R scalar. An R-algebra
endomorphism fixes every ground scalar. A program updating the numerical
scalar q by ordinary repeated squaring consequently does NOT satisfy this
contract. External tracking of those changing numerical bases is outside
the obstruction.

This contract is narrower than an arbitrary scalar algorithm. Level-
dependent quotients, representative-dependent maps with explicit correction
terms, finite-prefix moving carriers, sparse implicit circuits, and scalar
identities requiring no invariant algebra are outside it.

## 2. New arithmetic thinning: doubling itself has a long order

Use the SAME actual balanced prime-pair supply retained by the current
Hensel-spectrum audit. Its scale is P,Q in [c*M^3,C*M^3], with

    p-1=v_p*R_p,  R_p prime,  R_p>p^kappa,
    kappa=.677,   1<=v_p<=V=C_0*M^.969.               (B3)

The registered N-only seed and auxiliary-prime choices give exact local
orders ord_p(gamma)=ord_p(alpha)=R_p, uniformly over the allowed first-K
candidate m comparable to M. In particular R_p is odd and does not divide
m. Existing Hensel and unequal-exponent deletions preserve
Omega(M^6/log^2 M) actual inputs and have total loss soft O(M^5.994).

Fix tau=1.010 and T=floor(M^tau). Delete an input if, in either field,

    ord_(R_p)(2)<=T.                                 (B4)

This is proof-side deletion, not an algorithm for recovering hidden orders.
Every exceptional prime R_p divides the nonzero integer

    Z_T=prod_(1<=k<=T)(2^k-1).

Since log|Z_T|<=log(2)*T(T+1)/2 and
log R_p>=3*kappa*log M+O(1), at most O(T^2/log M) different admissible
exceptional primes R can occur. For each such R, every p in the supply is
of the form vR+1 with 1<=v<=V, giving at most V possible p integers.
There are O(M^3) possible partner integers in the balanced factor bin;
discarding primality and selector restrictions only overcounts. Taking
the union for BOTH fields therefore deletes at most

    O(M^3 * V * T^2/log M)
      = O(M^5.989/log M)                              (B5)

actual input pairs. No auxiliary-prime, center, phase, row, or seed menu
factor is added: R_p is the same exact local prime order under all those
already registered choices, and (B4) depends only on that prime.

Unite this deletion with the old deletions on the ORIGINAL supply, rather
than applying a fresh distribution statement to an already thinned set.
The old soft M^5.994 bound still dominates, and the same asymptotic majority
survives with

    ord_(R_P)(2)>M^1.010-1,
    ord_(R_Q)(2)>M^1.010-1.                          (B6)

For any fixed 1<tau<3*kappa/2=1.0155, the identical proof yields loss
O(M^(6-3*kappa+2*tau)/log M). The particular tau above is chosen to leave
the already registered dominant exponent 5.994 unchanged.

## 3. An invariant finite algebra needs the full doubling orbit

**Lemma.** Let K be a field, let B be a finite-dimensional commutative
unital K-algebra, and let sigma:B->B be a K-algebra endomorphism. Suppose
g in B and a K-algebra character phi:B->K satisfy

    sigma(g)=g^b,  phi(g)=z,

where z has prime multiplicative order R and R does not divide b.
Then

    dim_K B >= ord_R(b).                              (B7)

**Proof.** Put h=ord_R(b). For k=0,...,h-1 the characters
phi_k=phi composed with sigma^k satisfy phi_k(g)=z^(b^k). These h values
are distinct: equality is equivalent to b^k=b^ell modR. Thus the kernels
of phi_k are h distinct maximal ideals. Each character is surjective
because it fixes K, so the quotient by each kernel is K. Distinct maximal
ideals are pairwise comaximal. The Chinese remainder theorem gives a
surjection B onto K^h, and therefore dim_K B>=h. No reducedness,
semisimplicity, invertibility of sigma, or generic coefficient premise is
needed. The value z is a unit; g need not be assumed a unit in B. QED.

Reduce the contract in Section 1 modulo either hidden prime p. Since A is
finite FREE of rank d, its reduction B has dimension d. The reduced
sigma_0 is a unital F_p-algebra endomorphism fixing scalars, g=Qbar has
phi(g)=alpha modp of exact order R_p, and sigma_0(g)=g^2. The lemma and
(B6) prove

    d >= max(ord_(R_P)(2),ord_(R_Q)(2))
      > M^1.010-1.                                   (B8)

This applies to any finite-free algebra, not only a univariate quotient
or a quotient with monomial relations. Public inverse-index/Hensel
relations and arbitrary extra variables cannot produce a smaller algebra
meeting the same endomorphism and source-evaluation requirements.

## 4. The resulting acquisition obstruction and its exact boundary

In a dense basis-coordinate implementation of this contract, acquiring
even one complete algebra element requires d residue-word slots. On the
retained actual majority, (B8) forces Omega(M^1.010) slots, and therefore
Omega(M^1.010) bit writes even before arithmetic or parameter acquisition.
Since every allowed m is comparable to M, this exceeds soft O(m).
Known modular-composition improvements cannot turn a NONEXISTENT rank-
softm invariant source algebra into one. At the larger required rank,
their degree parameter still counts the representation being manipulated.
No lower bound is asserted for a compact implicit representation that
avoids these dense writes.

This is a new base-changing q-product obstruction. The older registered
partner/centered quotient theorems already rule out the different fixed-
q substitution X->alpha*X in a small unit-root carrier; that old result
is not counted as new here. The new arithmetic condition concerns the
order of 2 MODULO the hidden prime R_p, and (B2) changes Q itself.

An optional INPUT-INDEPENDENT dyadic library of radices also has the same
obstruction. For example take every integer 2<=b<=ceil((log M)^C) for
a fixed C. This entire library has polylogarithmic cardinality and every
b<R_p eventually. Replace 2^k-1 by b^k-1 in the proof, unite exceptional
primes over the whole library, and pay its cardinality and log b. The
additional loss remains soft O(M^5.989), uniformly before adaptive choice
inside that fixed library. The identities split i into residues modulo b
and require an abstract Qbar->Qbar^b endomorphism; (B7) then applies.
The special maps Qbar->Qbar or Qbar->Qbar^(-1) are not covered. Arbitrary
input-dependent radix libraries and larger radices remain open.

The fresh primary modular-composition inspection was Kedlaya--Umans,
*Fast polynomial factorization and modular composition*, Theorems 7.1
and 7.7 and the definition in Section 1.1. They compute supplied polynomial
composition/power projection with the degree parameter retained. Their
finite-ring bounds require supplied interpolation points whose pairwise
differences are units and are stated as d^(1+delta), with refined lower
order factors discussed separately. They do not claim a strict softm
q-product theorem from an unstable or missing invariant quotient.
[Primary paper](https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol08381/DagSemProc.08381.5/DagSemProc.08381.5.pdf).

No composite-ring division is hidden in the new theorem: (B1) divides only
by known source units, (B2) is division-free, and (B7) is a proof after
reduction to the two hidden fields, not a request to compute that reduction.
The finite-algebra route is excluded even if every public origin and every
required algebra operation is granted free except the specified dense
state acquisition. Correctness or coverage of a different implementation
is not inferred from this grant.

The exact long product still detects ANY zero. Its unrestricted implicit
scalar acquisition, proper factor separation/recovery and full deterministic
all-semiprime bit-clock proof remain open. No examples, new Lean certificates,
or backend runs are premises of this obstruction.
