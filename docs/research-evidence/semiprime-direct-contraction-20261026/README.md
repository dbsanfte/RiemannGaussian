# Joint coefficient actions, ternary rows and direct residue readout

26 October 2026. Continuation of the [fast-projective investigation](../semiprime-fast-projective-20261026/README.md), using three Sol 6.1 investigations, cross-reviews and a primary-agent audit.

**There is a new nearly linear coefficient operation, but no whole-query speedup.** All sections of the long q-product now share one explicitly initialized rational-Newton transform, whose forward and transpose actions cost soft K. The full ternary root hierarchy and an amplitude-free collision indicator are also derived. The remaining matched diagonal or singular residue has not been acquired at that cost. The best completed native weighted query remains soft K^(5/4), and the uniform two-monic fallback soft K^(3/2). The all-semiprime sixth-exponent and bit-complexity goals remain open.

Here K is the preparation scale, H=K², h=2H+1 and the native row count J is of order K. All cheap-operation claims retain the existing composite-ring factor-or-unit guards. These are paper results, not implementation or Lean certificates.

## 1. The coefficient sections are one executable transform

Write

    G_h(X)=product_(i<h)(1-rho^i X)=sum_t a_t X^t,
    rho=q^-1, A=rho^h, B=K, M=2K.

For t=Bs+e with s<M and e<B, the exact coefficient formula is

    a_(Bs+e)=alpha_s A^e
               (A^-1 Z_s;rho)_e/(rho Z_s;rho)_e,
    alpha_s=a_(Bs), Z_s=rho^(Bs).

The notation (z;rho)_e means product_(r<e)(1-z rho^r). The full blocks end at h-2; both h-1 and h are retained as explicit tails.

One q-factorial block polynomial and prefix products acquire ALL alpha_s in soft K. Clearing the common denominator converts the section kernel into a mixed prefix/suffix polynomial basis. A balanced product tree and monic multipoint evaluation then apply the entire kernel, or its transpose, to a supplied vector in soft K. Every inverted denominator is already certified by the short-clock unit screen. This is an actual initialized operation, not a compact name for K² coefficients.

For a supplied functional ell on the row quotient algebra, let b_t=ell(X^t mod F). On the paid separated branch write b_t=sum_j lambda_j y_j^t. The full-block scalar becomes

    sum_j lambda_j
      [V_B^t diag(alpha) Kernel V_1]_(j,j),
    V_B(s,j)=(y_j^B)^s, V_1(e,j)=y_j^e.

Each factor has cheap actions. The diagonal uses the SAME root on both sides, however, and is not an arbitrary single vector action. Literal completion costs soft(JK), so the older product engine remains better. A uniform linear-in-ell algorithm for this scalar would, under the stated transposition conditions, also acquire G_h mod F.

See [qbinomial-joint.md](qbinomial-joint.md) and its [review](review-qbinomial.md).

## 2. Test the new input against modular composition

The coefficient matrix C_(s,e)=a_(Bs+e) has an exact rank-one generalized displacement. Its boundary is supplied by the same already acquired block starts. Thus the new fast coefficient actions are concrete input for a composition attempt that previously lacked an acquired outer polynomial.

The power graph U_j=y_j^B and its inverse interpolation y_j=H(U_j) are also acquired in soft J: K-rough local orders make raising to B=K injective, and the existing separation guards pay the interpolation. This gives a legitimate graph on which to evaluate the implicit bivariate coefficient polynomial.

The [2026 two-relation-matrix composition algorithm](https://arxiv.org/html/2601.17422v1) was checked at its actual partial-sum and reduction steps. Its smaller exponent cannot simply be applied to our K-by-K coefficient input with only J~K graph points. A structure-aware relation reduction remains necessary. In the direct q-shift compression, division by the graph polynomial introduces an explicit quotient-evaluation correction. The boundary operator can have full row rank even though its forward and transpose actions remain cheap. This is not a lower bound for the actual correlated correction or diagonal.

See [composition-hybrid.md](composition-hybrid.md) and its [review](review-composition.md) for the exact displacement, native guards, source contract and unresolved contraction.

## 3. All ternary coefficients have a parent/character formula

At pure K=2*3^e, put delta=K/3 and q0=pi^(delta²). Reorder the three children of a parent by their coefficient lift r=0,1,2. Their actual roots satisfy

    y_r=p U^r q0^(c_r),    |c_r|<=7.

Here p is the acquired parent root, U is an acquired geometric-progression character, and every c_r is a public integer carry. The identity holds globally over the native ring. It gives all three elementary symmetric coefficients of the child cubic, refining the earlier determinant-only relation. Both good monic orientations interpret U using a quotient of the smaller factor; no hidden quotient digit is assumed supplied.

The characters themselves satisfy an exact cross-level recursion. Consequently the entire finite hierarchy is initialized in soft K. The A2/SL3 cubic-Adams formulas and coarse-tag first jets can be executed with these coefficients, but the tested execution retains the long clock. Neither a cubic norm nor a literal parent-window replacement has yielded a power saving. A reconstructed tighter parent window is not ruled out by that cost calculation.

See [ternary-fusion.md](ternary-fusion.md) and its [review](review-ternary.md).

## 4. Specify the desired hit indicator without its amplitude

In the acquired separated row algebra E=B[X]/F, choose the certified unit b=F_companion mod F, or simply b=1. Componentwise Laurent expansion gives

    Pi=b [delta^0] delta
         sum_(i<h)(1-q^-i X+delta b)^-1.

Every row has at most one clock hit, so Pi is precisely its 0/1 hit idempotent. Its ordinary and tag-weighted traces are (1,w_hit) at the good unique-hit field. This removes the unknown product amplitude from the output specification and needs only a simple pole, even when another component has several hit rows.

The residue is still unpaid. A mixed-component Laurent inverse is not ordinary power-series inversion with a unit constant. The known completion uses the existing long product engine.

A rank-one q-bispectral construction from [Gekhtman–Kasman](https://arxiv.org/html/math-ph/0408038) was also explicitly specialized and computed in soft J. Its output is a linear polynomial q-antiderivative of F. Its poles describe all row roots, so it does not by itself select the clock intersection. This identifies exactly what that integrable-systems formula supplies, without treating a tau-function identity as a fast singular solver.

See [singular-solve.md](singular-solve.md) and its [review](review-singular.md).

## Next substantive target

The best new combination is the acquired coefficient transform, the acquired power graph and the ternary root hierarchy. The required advance is a joint matched-diagonal or relation-reduction algorithm using those inputs, with the finite tails and quotient correction retained. A direct simple-pole extraction for Pi is a second precise target. Neither requires constructing the full matrix as part of its specification; neither has a proved soft-K execution yet.

The source contracts, paper-review status and preservation checks are recorded in [sources.json](sources.json), [review.json](review.json) and [manifest.json](manifest.json). The archive preserves 974 prior protected files, both document prefixes and 23 concurrent files. No factoring implementation, numerical campaign, Lean/public assets, commit or push was performed.
