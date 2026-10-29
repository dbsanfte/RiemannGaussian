# Executed self-dual q-Racah transform at the native half-clock boundary

2026-10-26. The calculation below tests a concrete finite quantum-6j/Racah duality, including its terminal normalization. It supplies an exact self-dual parameter choice and executes the terminal specialization. The resulting boundary is the original long half-kernel, not a shorter acquired evaluation. No soft O(L+sqrt m) algorithm or general obstruction is proved.

Prior Christoffel/Toda full-support and far-boundary audits, the finite descendant reports, and the latest native half-center/induction packets were read. Their determinant identities and short startup data are not counted again as progress.

## 1. Native query and a self-dual Racah family tailored to it

Use the acquired half-center quotient with degree L,

    C_m(W)=prod_(s=1..m)(W-q^-s-q^(s+1)),
    W=X+q/X,

and its equivalent odd-stride knot norm. All native X are supplied units, split as beta^(a+bN+lambda). Assume m>=2; m=0,1 are direct. Work in a range where 2m+3 is below both local q-orders, satisfied at the native asymptotic scales m=Theta(k^(3/2)), ord(q)>16k². Finite exceptional small scales can use the inherited fallback; no new order is acquired.

Choose q-Racah parameters

    N_R=m-1,
    alpha=beta_R=q,
    gamma=q^-m,
    delta_R=q^(m+2).

The parameter beta_R is a Racah parameter, not the arithmetic beta. The spectral variable is

    mu(z)=z+q³/z.

For n=0,...,m-1 set

    R_n(mu(z)) = sum_(j=0..n)
      (q^-n,q^(n+3),z,q³/z;q)_j*q^j
       /[(q,q²,q^(m+4),q^(1-m);q)_j].                 (1)

Here (a_1,...,a_r;q)_j denotes the product of the r Pochhammer symbols. Equation (1) is the standard terminating 4phi3 definition specialized to the displayed parameters. It is a polynomial of degree n in mu, because

    (z,q³/z;q)_j
      =prod_(r=0..j-1)(1-mu*z0_r+q^(2r+3)),
      z0_r=q^r.

On the finite spectral grid z=q^-x, x=0,...,m-1, the four upper parameters are q^-n,q^(n+3),q^-x,q^(x+3). Hence termwise permutation gives the exact self-duality

    R_n(mu(q^-x))=R_x(mu(q^-n)).                       (2)

Also mu(q^-(s-1))=q*(q^-s+q^(s+1)), so this is exactly the native half-clock grid after scaling W by q.

## 2. The finite transform is legal over the actual composite ring

No target/collision values occur in the lower parameters. For j<=n<=m-1, every scalar denominator in (1) is a product of q-units and nonzero short differences 1-q^a. The negative exponents in (q^(1-m);q)_j range only from 1-m to -1, never zero. The other exponents are bounded by 2m+2. They are certified units by the local-order guard.

The leading coefficient of R_n in mu is a unit: its terminal j=n coefficient contains only nonzero short scalar q-differences and q-powers. Finite spectral node differences are

    mu(q^-x)-mu(q^-y)
      =(q^-x-q^-y)*(1-q^(x+y+3)),

with x+y+3<=2m+1. Thus they are units as well. Consequently the m-by-m evaluation matrix [R_n(mu(q^-x))] is invertible over R, directly by its triangular polynomial-basis change followed by a unit Vandermonde. This avoids importing positivity, complex orthogonality, or unspecified field pivots. A normalized 6j basis change may be replaced by this unnormalized polynomial version, avoiding square-root norm choices.

The parameters, scalar powers, and initial R_0=1 are cheap to acquire. This is not an acquired full transform: emitting its m² entries is already too expensive. Generic finite-transform orthogonality does not establish a sublinear-in-m terminal contraction.

## 3. Execute the proposed terminal duality rather than crossing its singularity

The needed clock null polynomial is degree m, one above the finite Racah family. At n=m, the lower Pochhammer

    (q^(1-m);q)_m

contains 1-q^0=0. Thus R_m in normalized formula (1) is undefined there; one cannot use finite self-duality (2) to assign it a zero or an ordinary additional 6j row.

Clear the lower parameters symbolically before specializing. Define the degree-m polynomial

    T_m(z)= sum_(j=0..m)
       (q^-m,q^(m+3),z,q³/z;q)_j*q^j/(q;q)_j
       *prod_(a in {alpha*q,beta_R*delta_R*q,gamma*q})
                                      (a*q^j;q)_(m-j),   (3)

with the displayed parameter values substituted only in this polynomial expression. This is the product (alpha*q,beta_R*delta_R*q,gamma*q;q)_m times the generic normalized Racah polynomial, after exact cancellation of its scalar lower factors. No target numerator is canceled.

For every j<m, the gamma factor in (3) contains 1-q^0 and vanishes. At j=m its length is zero. Therefore the entire specialization is its last summand:

    T_m(z)=(-1)^m*q^(-m*(m-1)/2)
                    *(q^(m+3);q)_m*(z,q³/z;q)_m.      (4)

The scalar follows from (q^-m;q)_m=(-1)^m q^(-m*(m+1)/2)(q;q)_m. For a native row choose z=qX. Then

    (z,q³/z;q)_m=(qX,q²/X;q)_m
                =(-1)^m q^(m*(m+1)/2) C_m(X+q/X).

Hence the cleared terminal Racah polynomial is exactly

    T_m(qX)=q^m*(q^(m+3);q)_m*C_m(W).                  (5)

The prefactor in (5) is a unit and can itself be numerically acquired by the ordinary scalar Pochhammer algorithm in soft O(sqrt m). Thus the normalization is genuinely payable; the remaining quantity is precisely C_m(W). The terminal-collapse computation is an identity valid at every collision over R, not a limiting analytic argument.

**Outcome of this executed transform:** finite self-duality is nonsingular inside its m-dimensional support, but the normalized terminal row is outside that support. Correctly clearing its zero denominator returns the desired long kernel as a single terminal Pochhammer. It does not reduce m, shrink the acquired degree, or initialize its values modulo the native degree-L quotient.

## 4. A second concrete initialization: use the last legal row's endpoint values

This is a more plausible alternate start than declaring R_m to be known. The standard q-Racah endpoint summation gives, at x=m-1,

    R_n(mu(q^-(m-1)))
       =q^((m+2)n)*(q^-m;q)_n/(q^(m+4);q)_n.           (6)

Combining (2),(6) initializes the last legal row on every *integer grid point*:

    R_(m-1)(mu(q^-x))
       =q^((m+2)x)*(q^-m;q)_x/(q^(m+4);q)_x,
       0<=x<=m-1.                                    (7)

All denominators remain scalar units. A supplied integer x permits scalar Pochhammer evaluation in soft O(sqrt m), and short adjacent endpoint packets can share scalar factorial startup. This is an actual alternative endpoint formula, not unspecified starts.

However a native supplied z=q*beta^E is not supplied as q^-x with an integer x in that grid. Such a label would be the relation beta^(E+H+Hx)=1, which is exactly a native row/clock relation when it lies in the target window. It is not an acquired spectral coordinate. Different residue fields may give different coordinates, or z may lie outside their q-subgroups; the known integer E does not make E/H an allowed integer degree.

Consequently (7) does not evaluate the needed last legal row at arbitrary native W. Interpolating its full degree-(m-1) polynomial from the grid has soft O(m) input/output scale, above the target. A new algorithm computing only its modulo-G projection or norm in soft O(L+sqrt m) could genuinely initialize a terminal recurrence, but that projection is not supplied by ordinary finite duality.

Canceling the equal upper/lower parameter q^(1-m) in R_(m-1) does not remove this issue: the original finite sum stops at m-1. Extending the resulting shortened hypergeometric symbol to an infinite series at arbitrary z would add unlicensed terms. Formula (7) is asserted only at its stated integer spectral points.

## 5. What a native fusion initialization would have to add

This Racah family uses the exact paired parameters z=qX and q³/z=q²/X, whose product q³ encodes the already acquired opposite pairing. It has not used any arithmetic involving two different (a,b,lambda) labels. A new 6j/Bailey/Sears contraction must therefore supply a cross-row condition beyond that reciprocal pair if it is to improve the whole-family norm.

The native conic information is

    beta^(lambda²)=beta^(4abN)*q^c,
    c=(lambda²-4abN)/H in Z.

It is a carried quadratic relation in the integer exponents, not an automatic linear balancing of the Racah parameters. A proposed fusion that omits q^c would alter the input. The previously paid selected-shift screens also show that ordinary same-q parameter strings supply only short native chains on their continuing branch. Thus neither an unacquired integer dual label nor a fictitious torsion specialization supplies the missing initialization.

A genuinely useful alternate initialization would acquire both top legal **row residues modulo G** in soft O(L+sqrt m), after their unit leading-coefficient normalizations. One multiplication by the scaled variable mu=qW and the final monic three-term recurrence would then yield the cleared terminal row, with O(L) further work, provided its scalar-unit coefficients are derived and acquired. This must not import the normalized R_m recurrence through its zero denominator. This is a stronger-than-scalar acquisition target, not supplied here. A weaker alternative is a directly acquired certificate for the **coupled norm of that terminal linear combination**, retaining its cross terms. Separate scalar norms of the two legal rows are insufficient: a norm does not turn addition into addition. Such a joint native identity would need soft O(L) data and soft O(sqrt m) scalar endpoints, with every remaining denominator scalar-unit or factor-revealing. The current calculation exhibits the legal top-row endpoint that is actually available and the exact off-grid projection still to be initialized; it does not claim the missing certificate.

## 6. Primary sources and scope

- Tom H. Koornwinder, *Dual addition formulas: the case of continuous q-ultraspherical and q-Hermite polynomials*, Ramanujan Journal 61 (2023), 425–444, [primary article](https://link.springer.com/article/10.1007/s11139-021-00426-7); [author preprint](https://staff.fnwi.uva.nl/t.h.koornwinder/art/2017/2017_SSFA.pdf), §3.5 equations (3.18)–(3.23). The q-Racah 4phi3 definition, finite parameter range, and endpoint summation are used. The terminal specialization (3)–(5) is directly derived here.
- Paul Terwilliger, *Leonard pairs and the q-Racah polynomials*, [arXiv:math/0306301v2](https://arxiv.org/html/math/0306301), 2008 revision, LAA DOI 10.1016/j.laa.2004.02.014. It develops the field-based tridiagonal/diagonal pair framework and duality. No fast finite-ring norm theorem is claimed from it; the transform's unit assertions above are independently proved.
- Erik Koelink and Hjalmar Rosengren, *Harmonic analysis on the SU(2) dynamical quantum group*, Acta Applicandae Mathematicae 69 (2001), 163–220, [arXiv:math/0010093](https://arxiv.org/abs/math/0010093), DOI 10.1023/A:1013071729320. Quantum 6j/q-Racah orthogonality and recoupling provide the representation-theoretic setting, not a complexity bound or collision-safe arbitrary-target specialization.

No numerical campaign, repository edits, or backend lemmas were used. The paid full-family cost remains soft O(L+sqrt(Lm)); the exact zero-only prefix and signed/original-label consumer remain unchanged. This failure is scoped to the explicit self-dual finite Racah endpoint contraction, not to all bispectral algorithms or knot fusion identities.
