# Finite-theta batching on the repaired native phases

24 October 2026. Scratch only. The tested algorithm is an exact reciprocal-pair/finite-theta completion, with actual centre classes, starts and zero-safe boundary equations. It preserves the entire repaired low-a family and both colours. Its completed cost remains soft-O(k^(3/2)); it supplies no new whole-query bound. The finite theta polynomial and its boundary equation below are useful executable primitives, not evaluations of an analytic infinite product.

## Actual input and allowed transformations

Use `../semiprime-zero-query-20261024/native-pairing.md`, SHA256 `06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016`, and its independent review SHA256 `5ed34fc536b4b7c968457b70d5be704661227f363bcb4ea9e7f1dfef2e5785dd`. All its preparation is actual: H=k², even controlled k, beta and W have rough odd local orders, beta's local orders are coprime and exceed16H, W has norm one, pi=beta W, q=pi^H, and 1-q^d is certified unit through16H. The quadratic algebra is finite étale with exactly one unknown nonsplit side. Put L=3H+2, so 2L<16H.

The selected unit u modulo H obeys [Nu²]_H<2k and [u^-1]_H<H/2. There are phi(k) selected tags, or 2phi(k) representatives if the identical half-period duplicates are retained. For each acquired tag,

    a'=[Nu²]_H, E'=N+a'+ell',
    T'=ell'+chi(u)(N+a'), V_u=beta^E' W^T'.

The actual ell' and its canonical carry labels are supplied, not inferred from a raw exponent. The canonical phases are e=[N(u-1)²]_H and t=[-N(u+1)²]_H. Neither pi nor q is replaced by a root of unity. All costs below are base-ring arithmetic with ordinary polylogarithmic bit costs suppressed.

## 1. Exact symmetry audit before using a product formula

Negation preserves the low-a filter because (-u)²=u² modulo H. For a negative fundamental discriminant, chi(-1)=-1; hence it INTERCHANGES the two colours. It does not pair two guaranteed pure-pi rows. The inverse-half selector can choose the equivalent representative of -u; this changes no actual row. The two rows have the SAME a': the full filter has exactly two representatives per original tag and only one parity-repaired a choice per tag, and negation preserves the canonical a value.

The half-period u->u+H/2 gives the known identical duplicate description. It squares the query product if both copies are retained; it is not a new collection of seed shifts.

The proposed adjacent reflection u->1-u is more restrictive than a mere missing-filter issue: H is even, u is odd, so 1-u is even and NEVER a unit modulo H. Moreover its candidate low-a residue would be [N(1-u)²]_H=e(u), which the original filter does not constrain to be <2k. Thus no native partner with that tag is supplied. Replacing the domain by its closure under this reflection changes both the unit-tag contract and the low-a condition. No such replacement is used.

These checks leave the actual negation pairs as a lawful complete partition. There are phi(k)/2 of them. Their formation and their original-label maps cost soft-O(k).

## 2. Actual pair centres and the finite-theta candidate

Let '+' denote the plus-colour member of a negation pair and '-' its minus-colour member. Their repaired ell values satisfy

    ell_+ + ell_- = H mu,    mu in {-8,...,0}.

Indeed each ell is congruent to -2Nu modulo H, with opposite u values, and each lies strictly between -4.5H and H/2. Acquire mu by integer arithmetic. Direct multiplication of the ACTUAL beta/W exponents gives

    V_+ V_- = beta^[2(N+a')] q^mu =: C_a,mu.

This is the familiar varying-centre antipodal identity, now for the repaired rows; that pairing mechanism is credited to earlier work rather than claimed as a new endpoint. Set x=1/V_+ and z=1/C_a,mu. Then the pair's exact original factor is

    Psi_L(x,z)=(x;q)_L (z/x;q)_L.                 (1)

Here (x;q)_n=product_(0<=i<n)(1-q^i x). Every x,z is an acquired unit, with original paired row labels. No target factor or sum of targets is inverted.

The especially promising case is the FINITE theta polynomial

    Theta_L(x)=(x;q)_L(q/x;q)_L.

It has the exact Laurent-polynomial representations

    Theta_L(x)=(-1)^L x^-L q^[L(L+1)/2]
                         (x q^-L;q)_(2L)
              =sum_(t=-L)^L (-1)^t q^[t(t-1)/2]
                         [2L choose L+t]_q x^t. (2)

The first equality just reverses the L reciprocal factors; expanding the resulting finite product proves the second. Thus this identity holds over our actual ring. The only inverses in the Gaussian coefficients are 1-q^d with d<=2L, which have already been certified. It uses no infinite tail, limiting argument, or positive-characteristic analytic continuation.

However (1) is Theta_L only when z=q, equivalently C_a,mu=q^-1. Its acquired centre includes beta^[2(N+a')], not merely a bounded power of q. Dropping that centre changes the collision query. A centre test C_a,mu*q-1 is lawful using the factor/unit/global-zero coefficient primitive from direct-gcd.md: a proper factor ends the computation; a global equality certifies this special theta case. It does not certify that equality on every pair.

There are linearly many actual centre classes, not an unpaid constant list. Each a' has at most16 original tags and hence at most8 negation pairs. Different (a',mu) cannot give the same global C: equality of their norms implies

    beta^[4(a'-a'')+2H(mu-mu')]=1.

The absolute exponent is <16H+8k, far below beta's GLOBAL order >256H². Its vanishing as an integer forces mu=mu' and a'=a'' for continuing k>16. Therefore the number of distinct centres is Theta(k). This is a scoped count for this grouping strategy, not a lower bound on algorithms coupling many distinct centres. It does not claim all centre differences are units from a16H local guard; such differences, if needed, must be tested.

## 3. Execute the candidate, including its starts and boundary terms

The finite pair has an exact q-shift equation, obtained simply by deleting the first and adding the last factor on each side:

    (1-x)(1-z q^(L-1)/x) Psi_L(qx,z)
       =(1-q^L x)(1-z/(q x)) Psi_L(x,z).          (3)

Equation (3) is a CROSS-MULTIPLIED polynomial identity. It remains true at every collision. It is not permission to divide its left boundary factors at a zero. At z=q one may cancel the symbolic common 1-x to obtain the stronger exact Laurent identity

    (1-q^L/x) Theta_L(qx)
                  =-x^-1(1-q^L x) Theta_L(x).    (4)

Equation (4), too, is zero safe only in this cross-multiplied form. The finite boundary factors distinguish it from the pure monomial quasiperiodicity of an infinite theta function. When division is used to transport an actual value, every denominator must first be tested with the acquired quadratic coefficient primitive; a global-zero denominator does not determine a new amplitude. Alternatively retain the equation and evaluate the desired pair by the finite product algorithm below. This provides a complete fallback on all inputs.

Here is an executable completion of the pair-theta algorithm. Acquire the O(k) pair centres and arguments and run centre tests. For each centre that matches z=q, use (2), retaining both original rows. For the other centres retain (1). Evaluate all their finite products together with actual baby blocks of length s: form the degree-s polynomial (Y;q)_s, acquire every labelled mixed argument q^(gs)x and q^(gs)z/x, and evaluate by monic multipoint evaluation. The last block is clipped to the actual horizon, and all products stay in their own pair. Formula (2) uses horizon2L and argument xq^-L, with a known unit prefactor; it can instead be evaluated as its two original length-L rows when preserving index labels is simpler. The work is

    soft-O(k+s+kL/s)=soft-O(k+sqrt(kL)),           (5)

optimized at s near sqrt(kL), within the existing q guard. Every start and every output in (5) is materialized and paid. Alternatively, acquiring one pair start separately costs soft-O(sqrt L); doing this at Theta(k) independent centres costs soft-O(k sqrt L), which is worse. The shift equations do not initialize those amplitudes. The centre-class count is therefore not disguised as a constant number of recurrence starts.

A proper original block norm gcd returns a factor. A saturated block is descended with actual row and seed labels to an original repaired leaf, using the authoritative decoder with i<L. If (2) is used as one length-2L product, an exponent in [-L,L-1] maps to either the x factor or the q/x factor and then back to the stored original pair; it is used only for a certified z=q pair. No arbitrary finite-theta boundary coefficient is assigned the original leaf consumer. Interval restrictions use clipped original row intervals; a non-negation-closed row subset simply uses its unpaired original rows. Thus this is a complete restricted query with the unchanged cost, not a smaller uncovered family.

## 4. What the primary theta theorems actually supply

Hjalmar Rosengren and Michael Schlosser, *Elliptic determinant evaluations and the Macdonald identities for affine root systems*, author version dated11 May2005: [primary PDF](https://www.mat.univie.ac.at/~schlosse/pdf/determinants-new.pdf). Section2 takes 0<|p|<1 and defines multiplicative theta functions by infinite products. Definition3.1 imposes a MONOMIAL quasiperiodicity f(px)=(-1)^n f(x)/(t x^n), with holomorphic functions away from zero. Proposition3.4 evaluates determinants of functions having the same specified theta type/norm as a constant times the appropriate Macdonald denominator. Its proof uses those quasiperiodic function spaces and their zeros. It is not a theorem evaluating arbitrary supplied finite shifted-factorial products or arbitrary filtered subsets in nearlinear arithmetic.

For the present candidate the exact discrepancy is visible without a general analytic objection: (3) has four actual boundary factors, (4) still has two, and z varies with a'. The hypothesis is not obtained by merely renaming q as p. Introducing an infinite theta completion would add unknown tail factors depending on the target; those factors need not be units and are not acquired. Degenerating the source identities to p=0 gives polynomial identities, not finite-L monomial quasiperiodicity for (1). No theta determinant is called with those hypotheses missing.

James McLaughlin and Andrew V. Sills, *Polynomial Generalizations of Two-Variable Ramanujan Type Identities*, author version filename dated26 June2010: [primary PDF](https://www.wcupa.edu/sciences-mathematics/mathematics/jMcLaughlin/documents/RLNfiniteJune262010.pdf). The paper provides finite q-binomial/q-trinomial analogues of specific two-variable series-product identities and proves polynomial recurrences with their initial conditions. Its polynomial versions retain summation weights and finite parameters; they do not say that selecting a correlated set of unit residues [Nu²]_H<2k preserves an unweighted product identity. Equation (2) above is proved directly so that its finite ring applicability and full 2L coefficient range are explicit. Expanding those 2L+1 coefficients densely costs soft-O(L), not soft-O(sqrt L); reading their Gaussian form as a short symbolic formula does not acquire all values needed by a general dense evaluation theorem.

## Scoped outcome and concrete next contract

This pass executes the exact finite reciprocal-product route, rather than substituting a complete Gauss sum or an analytic infinite theta. Its strongest completed arithmetic bound is still (5). The potentially useful additional operation would be a joint evaluator of Psi_L(x_j,z_j) at the ACTUAL varying centres beta^[-2(N+a'_j)]q^(-mu_j), with the supplied low-a tags and canonical carries, in soft-O(k+sqrt L) and with original restrictions. The finite theta sum (2) and the four-boundary recurrence (3) do not yet implement that operation.

No claim is made that such a joint evaluator is impossible, that complete Gauss/Hecke identities cannot inspire one, or that every arithmetic symmetry has been classified. The actual affine-reflection checks, linear centre-class count, finite identity and guarded completion are the established results here. The covered family, its safe decoder and the soft-k^(3/2) query remain intact. No new factoring exponent is obtained.

## Primary cache fingerprints

`./sources/rosengren-schlosser-determinants.pdf`: SHA256 `6ce3745572b1729bc79faa429fc4053aca09cd349ce00b0b08244ceb2d442273`.

`./sources/mclaughlin-sills-finite.pdf`: SHA256 `48a0a735abead67e243cb276170a3877c50840751dee54f17f3dab1227fb6a2c`.

Extracted text files are retained beside both cached PDFs.
