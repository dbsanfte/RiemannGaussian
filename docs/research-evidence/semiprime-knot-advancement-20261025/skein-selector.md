# Native skein selector attempt, 25 October 2026

## Outcome

There is an exact bounded-width matrix/annular-trace encoding of each native swapped pair. The pair-first reduction and idempotent extraction below are already established in swap-erratum.md §3 and are retained only as context. I did not construct a soft-k selector among all pairs. The precise missing theorem is selection of one pair whose split quadratic meets the short q-orbit; it is weaker than computing the full catalogue q-product, but the published affine-slope and Chebyshev identities do not perform that selection.

This note uses the actual catalogue in `/tmp/semiprime-paired-weighted-query-20261024/scalar-catalogue.md`. It preserves signed 0<|ab|<k plus axes, all uncentered 0<=lambda<H roots, public global-integer zero-row deletion, local order assumptions, and the inherited annihilator extractor. No special-semiprime replacement is made.

## 1. A concrete pair-first route within the desired cost

For one surviving swapped pair with the same lambda, set

    E=a+bN+lambda, E'=b+aN+lambda,
    u=beta^E, v=beta^E'.

The parent task supplies the native coverage theorem: for some such pair and common i in [-M,M], z=q^i equals u at one prime and v at the other. Assume the paid preprocessing has either factored N or made u-v a unit for useful candidate pairs. The pair identities are exact:

    E-E'=(a-b)(1-N),
    E+E'=(a+b)(N+1)+2lambda,
    s=uv=beta^((a+b)(N+1)+2lambda),
    t=u+v.

Hence the native same-index mixed collision implies

    g(z)=z²-tz+s=0 mod N,
    e=(z-v)/(u-v), e²=e, e neither 0 nor 1 mod N.

A known mixed root z therefore immediately factors by gcd(e,N). Conversely, every mixed root of this split quadratic yields a factor. Pure roots u,v are public and yield e=1,0, so merely solving the split quadratic or diagonalizing it does not acquire the useful CRT branch.

**Useful cost reduction:** If one guaranteed pair can be selected in soft-k bit operations, no length-h query on all J rows is needed. Run the established block q-product evaluator on just these two rows, with block length d=ceil(sqrt h). Its cost is soft-O(d+2h/d)=soft-O(sqrt h)=soft-O(k^(3/4)) ring operations; log-N bit factors are absorbed by soft notation. Powers have O(log N)-bit exponents. Each target is a unit. Product-tree/MPE evaluation is monic and needs no target differences inverted.

At least one selected row has a local collision. A proper gcd gives a factor. Saturated row/index aggregates are localized with logarithmic overhead; the public zero-row deletion ensures the recovered K=E-Hi is a nonzero O(log N)-bit integer. A global leaf collision then invokes the already licensed short-annihilator extractor, costing soft-k. Thus the pair-first selector really is enough even when extra collisions cause saturation; it need not provide i itself or distinguish its primes.

This is established project material (swap-erratum.md §3), not new progress, a new implementation of the selector, or a new factoring bound.

## 2. Exact width-two character construction

For a candidate pair, form the entirely explicit companion matrix

    B=[[t,-s],[1,0]], det(B)=s unit.

Its characteristic polynomial is g. Since u-v is a unit, the two known eigenvectors (u,1)^T and (v,1)^T diagonalize B over R. The acquired rank-two algebra is

    A_pair=R[Z]/g(Z) ≅ R×R,
    Z -> (u,v).

This construction costs O(1) ring operations per pair after u,v, with one batched inverse or gcd preprocessing as supplied. All J matrices, labels and powers s,t cost soft-k bits. Its algebra dimension is 2 per pair, total O(J); no quantum-torus finite-dimensional representation is assumed.

Define the integral Dickson/Chebyshev-type polynomials

    D_0(T,S)=2, D_1(T,S)=T,
    D_(n+1)(T,S)=T D_n(T,S)-S D_(n-1)(T,S).

Then, without square roots or division,

    tr(B^n)=D_n(t,s)=u^n+v^n.

If z=q^i is the native mixed root, its complementary root is s/z, so

    q^i+s q^-i=t,
    q^(ni)+s^n q^(-ni)=D_n(t,s) for every n.

This is a genuine bounded-width trace encoding of the native collision, and one can acquire tr(B^n) in O(log n) ring operations by binary powering. It retains i symbolically in q^i. It does not determine i: the matrix, eigenvalues, and every symmetric trace are already computable from the public pure roots u,v, independent of the mixed CRT branch.

There is no automatic square-root normalization s^(1/2). Adjoining W with W²=s gives a rank-two extension and permits an SL2-style normalization, but neither supplies a scalar square root in R nor a nontrivial idempotent. Using D_n directly avoids the extension and its interpretation issues.

## 3. Which skein theorem matches this construction

Frohman–Gelca, *Skein Modules and the Noncommutative Torus*, https://arxiv.org/abs/math/9806107 and https://www.math.ttu.edu/~rgelca/torus6.pdf , gives

    E_v E_w=t0^det(v,w) E_(v+w)+t0^-det(v,w) E_(v-w).

For v_n=v+nw and d=det(w,v), this yields the exact constant recurrence

    E_w E_(v+nw)=t0^d E_(v+(n+1)w)+t0^-d E_(v+(n-1)w).

Thus one affine-slope curve, including its winding index, can be advanced through a fixed second-order recurrence. At commutative character specialization, the reciprocal trace identity is T_n(U+U^-1)=U^n+U^-n. The width-two construction above is its determinant-s generalization, realized directly by a GL2 companion matrix.

Lê, *On Kauffman bracket skein modules at roots of unity*, https://msp.org/agt/2015/15-2/agt-v15-n2-p16-s.pdf , Proposition2.2, supplies the annular formulas

    T_n(z0)·e=t0^n w^n+t0^-n w^-n,
    e·T_n(z0)=t0^n w^-n+t0^-n w^n.

These compress two reciprocal powers, not the search over which acquired pair admits a mixed q-orbit root. Theorem1/Proposition2.5 tie nonconstant transparency to root-of-unity conditions; those hypotheses are not supplied here. No such specialization is invoked.

The key distinction is operational: **advancing a known trace or slope index n is easy; finding the unknown collision index i from equality of two trace families is a discrete intersection problem.** Binary powering B^n answers a chosen n; it does not solve q^i+s q^-i=t over an interval without an additional intersection algorithm.

## 4. Does the catalogue discriminant supply the missing slope/index?

The catalogue has a suggestive exact arithmetic relation. Put

    sigma=a+bN, delta=a-bN.

Then

    sigma²-delta²=4abN,
    lambda² ≡ sigma²-delta² mod H.

The sum sigma is the sum of coordinates of lattice vector (a,bN), while delta is det((a,bN),(1,1)). This makes the discriminant look compatible with slope/area bookkeeping. However, the congruence is modulo the known integer H; the local collision is modulo the unknown multiplicative orders of beta. They are different moduli.

More explicitly, write lambda²-4abN=Hc, with known O(log N)-bit c. Exponentiation gives only

    beta^(lambda²-4abN)=q^c.

That phase identity is available cheaply for every catalogue row, including non-witness rows. It contains no small collision index. For the native witness, HI-lambda=aP+bQ (or the opposite orientation), and

    (HI-lambda)²-4abN=(aP-bQ)².

Selecting the correct short I means finding the relevant unknown square branch of this integer discriminant relation, with the factors P,Q still absent. The Frohman–Gelca determinant weights account for oriented area; they do not turn the displayed modular square-root condition into a known affine-slope coordinate I. Representing c or lambda by a large winding merely re-encodes public arithmetic already acquired.

The old uncentered catalogue issue remains: replacing (a,b) by (-a,-b) uses lambda'=(-lambda mod H), giving E_negative=H-E when lambda!=0, not -E. Inverse closure or centered traces must be explicitly acquired. The present swapped pair uses the SAME lambda and does not assume inverse closure.

## 4a. Explicit discriminant matrix candidate: successful modulo H, failed modulo N

Here is an actual native 2x2 candidate and a complete failure calculation, rather than an unspecified selector request. Let sigma=a+bN and define over the integers

    C_ab=[[sigma,4abN],[1,sigma]],
    det(ZI-C_ab)=(Z-sigma)²-4abN.

Modulo H, every acquired lambda supplies an eigenvector (lambda,1)^T with eigenvalue sigma+lambda=E mod H, since

    C_ab (lambda,1)^T - (sigma+lambda)(lambda,1)^T
      = (4abN-lambda²,0)^T = 0 mod H.

Thus the native arithmetic discriminant has an exact width-two spectral realization. All matrices and eigenvalue labels can be acquired in soft-k bit operations. It requires no inverse, so singular lambda branches and axes are retained.

But the factor-detecting coefficient ring is R=Z/NZ. In that ring 4abN=0, so

    C_ab mod N=[[sigma,0],[1,sigma]],
    det(EI-C_ab)=lambda² mod N.

The hard branch gives P,Q>16H and 0<=lambda<H. Hence if lambda!=0, lambda is a unit modulo N, and the purported E-eigenvalue determinant is a unit. If lambda=0, it is zero globally and the matrix has the same scalar eigenvalue sigma at both primes; this exposes no mixed branch and no factor. The native witness guarantee does not change either calculation. Binary powering of this matrix stays sigma^n I+n sigma^(n-1)K with K²=0, so any fast trace advancement merely returns 2sigma^n. It does not acquire beta^E=q^i or choose the pair.

The even simpler area candidate U(a)V(4bN), with U(r)=[[1,r],[0,1]], V(s)=[[1,0],[s,1]], has trace 2+4abN and likewise loses the discriminant modulo N. This proves failure of these explicit trace/area candidates, not of arbitrary matrices using beta^N in their entries.

Keeping C_ab modulo H preserves its eigenvalues, but supplies no ring map from Z/HZ into Z/NZ: gcd(H,N)=1. The exponent map r -> beta^r is not additive modulo H because beta^(r+H)=q beta^r, with q!=1 locally. Taking r to be its canonical representative introduces a carry q^c on addition. Consequently exponentiating the modulo-H eigenvalue does not define a matrix functional calculus over R. Lifting to integer entries does not fix the problem: lambda²-4abN is Hc, generally nonzero, so lambda is not an integer eigenvalue. Supplying beta^lambda separately gives precisely the already acquired row u; it does not create a trace selector.

This candidate is especially instructive: the arithmetic discriminant really is a small-matrix characteristic discriminant, but it lives in the known clock-modulus ring, whereas the mixed-root signal lives in the factor ring. A new constructive skein mapping must bridge these two rings while explicitly tracking the q-carry; a trace of C_ab alone cannot do that.

## 5. A precise sufficient new theorem

The following would complete the desired route; it is a theorem needed, not an established literature result.

**Native split-quadratic orbit selector.** Given the actual soft-k acquired list of swapped pairs (u_j,v_j), paid unit differences, labels (a_j,b_j,lambda_j), and q with the stated local orders, use soft-k bit operations to return either a factor of N or one list index j such that

    g_j(q^i)=0 mod N for some i in [-M,M],

with q^i a mixed root modulo the two primes. The theorem may instead guarantee any returned pair has at least one local hit; the two-row consumer in Section1 suffices. It need not output i, compute all g_j(q^i), evaluate the full C_M, or provide universal integer-divisor coverage.

For a bounded-width skein proof, a concrete sufficient output is a short, acquired tangle/coloring (or a bounded-rank algebra element) whose accessible coefficients expose such a row index through a binary partition of the supplied list. Required properties are: native witness coverage under every allowed N; a nonunit coefficient for some child containing a local-hit row; a termination certificate preventing a spurious zero from hiding all witnesses; and total cost of all coefficient acquisition plus O(log J) localization soft-k. Constant matrix width alone is insufficient if it scans h sites or hides h coefficients in an oracle.

The natural width-two matrices B_j above acquire all row data in soft-k, but their known traces supply no nonunit coefficient: B_j is already split at the public roots. A purported colored trace functional must explain exactly how it couples these matrices to the *interval* {q^i} without explicitly acquiring the h-element clock or the existing soft-k^(5/4) norm. This is the place a new skein identity, rather than further fast powering, is needed.

## 6. Localization, units, and complexity boundaries

- All direct pair/matrix arithmetic specializes integrally over R; no semisimplicity, Hecke projector, Jones–Wenzl denominator, or unknown square root is used.
- Pair differences are inverted only after the authorized preprocessing makes them units; failed unit tests return a factor.
- Public q^r-1 is a unit for 0<|r|<16H by both local-order bounds. Differences involving arbitrary catalogue exponents have no such automatic guarantee.
- The matrix algebra for one pair has dimension2, but h chosen evaluations of it still cost h; chosen-index binary powering costs logarithmic time and does not perform unknown-index search.
- Each modular operation has soft-O(log N) bit cost; all supplied labels/exponents have O(log N) bits. Acquiring J pair matrices is soft-k; acquiring h seed powers is soft-k^(3/2) and is not licensed as free input.
- The proposed selector must survive deletion of entire public zero rows. No full root-coset or skein tiling identity is used on a broken list.
- Returning a known pure root of g_j, or a symmetric trace that vanishes for unrelated reasons, is not enough. The permitted weaker pair output is one with a verified native-coverage theorem, followed by the two-row consumer and inherited saturation recovery.

No improved complete algorithm is claimed. The pair-first reduction is old project credit. The explicit new audit is Section4a: the native discriminant has a valid width-two realization modulo H, but the same candidate loses its discriminant modulo N, and exponentiation between these coefficient rings introduces the nonstationary q-carry. No working selector was obtained.
