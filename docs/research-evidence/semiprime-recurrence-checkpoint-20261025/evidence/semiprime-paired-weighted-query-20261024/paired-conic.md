# Exact paired Gauss conic and a charged support-basis test

24 October 2026. This acquires the full paired-basis conic and determines its EXACT integer content, including its scaled height in the honest index rectangle. A tested monomial basis in the known linear forms has a nontrivial charged determinant. No short index selector, extra root theorem or faster whole query is supplied. The current soft k^(5/4) signed-weight algorithm and open sixth-rate goal remain unchanged.

Prior input is /tmp/semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md SHA256 `b36e44e9d5e2c897caac87d6ad6339548fd9d438bd21352bd50971ff236efc93`, exact-source review `16b648c2556ae7b72864901a6a213672d18bce575a9c73114d15c1bf48c67eec`. Known residue-assisted factoring and primitive polynomial-height cautions are already audited in the earlier journal; no new known-bits threshold is claimed here. The second-vector and hard-basis bounds below were also checked by recurrence_adjoint_attempt in discussion.

## Actual full basis and affine factor coordinates

Let N=RS<=k^6, R,S>16H, H=k², and fix a public correct size bin B<=R<2B. For each unit tag j let Lambda_j={(a,b):a*j²=bN modk}. Acquire a FULL Gauss-reduced basis (a1,b1),(a2,b2) in the metric

    v_n=(a_n B²,b_n N), lambda_n=||v_n||,
    Delta=a1*b2-a2*b1=epsilon*k, epsilon in{+1,-1}.

It is a unimodular reduction of(k,0),([Nj^-2]_k,1), so gcd(b1,b2)=1. All basis operations are exact polynomial-logarithmic work; neither a balanced basis nor coprimality of an individual coefficient is assumed.

For each basis row acquire the existing t_n and centered ell_n from the signed-weight source. At the own tag j=R modk both

    I_n=(a_n R+b_n S+ell_n)/H

are integers. Inverting the two equations yields public affine forms

    L1=b2 I1-b1 I2, L2=-a2 I1+a1 I2,
    R=R0+epsilon*k*L1, S=S0+epsilon*k*L2,
    R0=(b1 ell2-b2 ell1)/Delta,
    S0=(a2 ell1-a1 ell2)/Delta.                 (1)

R0,S0 are INTEGERS. Write ell_n=-2a_n j+k t_n+H z_n and use the defining congruences t_n*j=(a_n j²-b_nN)/k modk. They give R0=j modk and S0=N/j modk. Thus this is an initialized integer coordinate system, not a rational reparameterization whose denominators are ignored.

## Conic content is exactly H

Define Q(I1,I2)=R(I)S(I)-N. Its quadratic coefficients contain k². Its linear coefficients also contain k², because b_n S0-a_n R0=0 modk. For its constant, the exact row equations a_n R0+b_n S0+ell_n=0 imply

    a_n R0²+ell_n R0+b_nN=b_n(N-R0S0).

The left side is divisible byH since R0=j modk and the native row polynomial vanishes on j+kZ. Since gcd(b1,b2)=1, H divides N-R0S0. Therefore Q/H is an integer conic.

There is NO additional integer content. Its homogeneous part after division byH is L1*L2. Before Gauss, basis(k,0),(s,1), s=[Nj^-2]_k, gives L1=I1,L2=-s I1+k I2, a primitive homogeneous polynomial since gcd(s,k)=1. Unimodular basis change preserves polynomial content. Hence the content of Q is EXACTLY H and Q0=Q/H is primitive. It is irreducible over Q: the invertible rational affine change(1) takes it to a nonzero multiple of XY-N, which is irreducible for N!=0. No resultant-independence heuristic is involved.

The index image under(L1,L2) has determinant|Delta|=k. It is not all Z², even though the original I coordinates are integral. Equivalently, the ordinary factor-residue hyperbola and this paired conic encode compatible index-k lattice constraints; neither supplies a new residue moduloH for free.

## Honest rectangle, including hard Gauss bases

Gauss reduction gives

    k B² N <= lambda1*lambda2 <= (2/sqrt3)k B² N.

In the correct bin |a_n|R+|b_n|S<=sqrt5*lambda_n/B. Thus the public norm-certified boxes may be taken as

    |I_n|<=X_n=ceil(sqrt5*lambda_n/(B H)+1/2),

using rational upward bounds on norms in the implementation. Since B>8H and N/B>16H, lambda_n/(BH)>8. Additive rounding is harmless, and this PARTICULAR certified rectangle has

    X1*X2=Theta(N/k³).                          (2)

This is the size of the acquired containing rectangle, not a lower bound on attainable conic points or a claim that its indices vary independently.

Individual widths can differ greatly. A useful universal upper bound is lambda2/B<k sqrtN on this hard branch. If v1 is nonaxis, lambda1>=sqrt(B⁴+N²), and the product bound yields lambda2/B<=sqrt(2/3)k sqrtN. If the coefficient pair(a1,b1)=(+/-k,0), full determinant forces b2=+/-1, reduction gives |a2|<=k/2, and reducedness forces B²<=2N/(sqrt3*k). Combine this with B>8H and N<=k^6 to get lambda2/B<k sqrtN. The other axis is symmetric, using a2=+/-1, |b2|<=k/2, its reverse aspect-ratio inequality, B<N/(16H), and the same bounds. Thus no hard badly-conditioned basis was discarded.

These bounds also determine the scaled primitive height. From(1), |R0|<=k*lambda2/N<B/16 and |S0|<=k*lambda2/B²<(N/B)/16, since sqrtN>16H. On the full box(2), each scaled linear contribution to R is O(B), and each to S is O(N/B): use lambda1*lambda2=Theta(k B²N) for the cross products. Hence

    W=||Q0(X1 Z1,X2 Z2)||_infinity=Theta(N/H).   (3)

The lower bound comes from |R0S0-N|/H>(255/256)N/H; the upper bound charges every quadratic and linear coefficient. This is the PRIMITIVE scaled height. Substituting rawN or N/k into a small-root inequality would be incorrect. At N~k^6 the rectangle product is Theta(k³) and height is Theta(k⁴), with both the k² content and the actual aspect ratio retained.

## Tested known-linear-form monomial basis

A natural support-aware test uses L1^a L2^b instead of I1^a I2^b. This is an explicit integer coefficient transformation. On homogeneous degree d its determinant has absolute value

    |det(L1,L2)|^(d(d+1)/2)=k^(d(d+1)/2),

the determinant of the degree-d symmetric power of the2-by-2 map. Through all degrees0,...,D, its absolute determinant is

    k^[D(D+1)(D+2)/6].                          (4)

The formula holds for ill-conditioned bases too; scaling coefficient columns by X1^a X2^b does not remove this relative factor. Thus transporting hyperbola monomials into the thin index lattice is not a free unimodular support change. This computes the determinant of this monomial family only. It is NOT asserted to be a complete Coppersmith auxiliary lattice determinant, a proof that every such lattice fails, or a lower bound on another affine-aware theorem. No guaranteed independent integer-zero polynomial or small covering index list was obtained by this test.

## Recent rank-three primary contract checked

Yiming Gao, Yansong Feng, Honggang Hu, Yanbin Pan, *On Factoring and Power Divisor Problems via Rank-3 Lattices and the Second Vector*, arXiv:2512.19076v1,22December2025, also ePrint2025/1004:
https://arxiv.org/abs/2512.19076
https://arxiv.org/pdf/2512.19076

Primary cached sources/gao-feng-hu-pan-2025.pdf SHA256 `dd71520d86c5a6b0a3bfa8dad495fcf26dfabee64c8e2b580e50cb0a9dc57c51`. The ePrint PDF endpoint returned403, so this audit uses the actual arXiv v1, not an unverified alternate version.

Algorithm4.3/Lemma4.4 form the UNIVARIATE rank-three lattice generated by N,f(xX),f(xX)², with f=x+j*m^-1 modN and X=floor(N^beta/m). The lemma assumes1/3<=beta<=1/2 and72<m<N^((1-beta)/2)/2. The first shortest vector is the explicit trivial(j,mX,0); their second LLL vector has a nonzero quadratic coefficient. Proposition4.5 derives a SMALL MULTIPLE g(x0)=i*p and still searches its index with BSGS. In the balanced case the quotient bound has scale sqrtN/m^(3/2); at m=k this is the current k^(3/2) index scale, not a polylogarithmic selector. Theorem1.1's balanced factoring bound improves logarithmic factors of the known N^(1/5) method. It is not a support-aware bivariate conic-root theorem or an all-factor-bin guarantee for our paired indices. The actual parameter restrictions are retained.

The completed output of this note is exact paired integer arithmetic, primitive content/height and a charged support-basis calculation, plus a primary applicability check. It supplies no faster candidate catalogue or root oracle. No finite samples, shared/frozen source edits, generic impossibility claim or new factoring record were used.
