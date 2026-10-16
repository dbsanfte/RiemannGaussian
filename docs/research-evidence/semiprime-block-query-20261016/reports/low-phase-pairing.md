# The inverse-reflection pairs cancel the next input digit, but have distinct centers

2026-10-15. Exact actual-source classification. No softly linear long-query algorithm or general complexity lower bound was obtained. The elementary digit-transport law used below is already compiled; it is not a new arithmetic coverage or carry theorem.

## Literal data and the proposed symmetry

Let m be an odd prime, m not divide N, d=m^2, and 1<=j<m. Keep the native data

    a_j = N j^(-2) mod m,  1<=a_j<m,
    D_j = (N-a_j j^2)/m,
    b_j = centered(m,-j^(-1)D_j),
    delta_j = a_j(1-2j)+m b_j,
    E_j=N+delta_j,  z_j=gamma^(-E_j),  q=gamma^d.

The inverse in b_j may be any integer representative modulo m; centered gives the same exact b_j. The public source satisfies -3d<=delta_j<=d. Write t=j^(-1) in F_m. Its old low-digit identity is

    delta_j = N(t^2-2t) mod m,
    E_j = N(t-1)^2 mod m.                          (1)

The nontrivial same-phase involution is t'=2-t, equivalently j'=j/(2j-1) in F_m. It is a valid distinct tag exactly when t is outside {0,1,2}. Thus j=1 is a fixed tag and j=2^(-1) has no partner among nonzero tags. The remaining m-3 tags form (m-3)/2 unordered pairs. This merely identifies explicitly the degree-two fibers already controlled by the native source; it is not a new fiber bound.

## Exact higher-input-digit cancellation

Write N=s+m u+d v with 1<=s<m and 0<=u<m. The literal delta_j depends only on N modulo d: when N increases by d, a_j is unchanged, D_j increases by m, and centered b_j is unchanged.

The old compiled offset_difference_modEq gives, or the same centered formula directly proves,

    delta_j(s+m u)-delta_j(s) = -m u t mod d.       (2)

Consequently

    E_j(N) = E_j(s)+m u(1-t) mod d.                (3)

For a genuine pair, t+t'=2 mod m. Adding (3) therefore gives

    E_j(N)+E_j'(N) = E_j(s)+E_j'(s) mod d.         (4)

This is the actual higher-digit cancellation: the pair-product phase modulo m^2 is independent of BOTH higher input digits u and v, at fixed N mod m. No integer equality modulo the unknown order of gamma is substituted for this congruence.

Define the publicly computable canonical center

    c_pair(s) = (E_j(s)+E_j'(s)) mod d,  0<=c_pair<d.

There is an EXACT known integer kappa_pair(N) such that

    E_j(N)+E_j'(N)=c_pair(s)+d*kappa_pair(N),
    z_j*z_j' = gamma^(-c_pair(s))*q^(-kappa_pair(N)).   (5)

Moreover kappa_pair(N)=floor(2N/d)+O(1), uniformly in the pair: the sum of two offsets lies in [-6d,2d]. Thus (5) does not conceal an unbounded row-dependent residual carry after the common huge exponent is removed. Computing these centers, sums and carries needs O(m) public arithmetic items plus the ordinary soft O(m) unit powering used for target metadata. It does not require the factors or local orders.

## The centers do not coalesce

For a pair, reduction of (4) modulo m gives

    c_pair(s)=2s(t-1)^2 mod m.                     (6)

Distinct genuine unordered pairs have distinct (t-1)^2: equality means t-1 equals plus or minus t'-1, hence gives exactly the same reflection orbit. In fact the center residues are precisely 2s times the nonzero quadratic residues other than 1. There are (m-3)/2 of them. Thus all canonical c_pair(s) are distinct as integers.

There is also an unconditional local distinctness conclusion on the inherited actual prime-order branch. At fixed N, let C_pair(N)=E_j(N)+E_j'(N). Two such integers differ by at most 8d, and (6) shows that their difference is nonzero modulo m, hence nonzero as an integer. If the local order of gamma exceeds 8d (in particular, the historical R_P,R_Q>16d supply), gamma^(-C_pair(N)) takes distinct values for distinct pairs in EACH hidden field. Likewise the q-normalized products gamma^(-c_pair(s)) are distinct, since their exponents lie in [0,d).

Therefore there is no one common reciprocal center for these pairs, nor a bounded number of exact product-center classes: the natural product-center collection has (m-3)/2 distinct members, even after the full higher input digits have been removed by the known q carries. This is an exact statement on the actual source, requiring no new deletion/counting argument. It is about these explicit pair products, not arbitrary row-dependent rescalings. Such rescalings can of course normalize any individual pair, but they move its common q-grid origin and must be carried through the long products.

## What this gives to an additive evaluator

The exact pairing factorization is public and ring-safe. For any formal X,

    (1-X z_j)(1-X z_j')
      =1-X(z_j+z_j')+X^2 gamma^(-c_pair(s))q^(-kappa_pair(N)).  (7)

Taking X=q^i and multiplying i=0,...,L-1 gives the paired long-row query. Formula (7) supplies the complete quadratic factors and their digit-stable product coefficients in soft O(m) metadata cost. It still asks for L evaluations of each quadratic, or another algorithm for their product along the long q-grid. It does not replace them by selected coefficients of one common Gaussian stream.

The centers' quadratic low residues alone are insufficient for a classical finite Gauss-period collapse: gamma has the actual large local orders, not order m or m^2, and equality of exponent residues modulo m is not equality of powers of gamma. A Fourier or character transform adjoining an m-th root of unity must still account for the full lifted phases c_pair(s), the known q carries, and the acquisition cost of all requested transforms. The distinct-center proof rules out the proposed common-center simplification, not every possible q-deformed Gauss-period identity or additive cancellation algorithm.

The actionable classification is thus precise: pairing cancels the next input digit in the product phase, but yields linearly many distinct public centers rather than a few shared centers. An additive method would have to exploit this nonconstant center family while acquiring the long q-grid products. No such paid method is established here. Merely grouping these quadratic factors changes the number of rows by a constant factor and does not improve the soft O(m^(3/2)) general acquisition clock.

## Provenance and scope

The adjacent source-pins.json pins the exact native definitions, old second-carry identities and old prescribed-gap mass theorem, as well as the historical actual prime-order premise. Prior journal investigation of antipodal and hyperbola pairings already warned that row-dependent normalization changes the baby origins; this report does not rebrand that old trace fold as a new algorithm. The specific inverse-reflection product-phase law (4)--(6) is the additional classification examined here. No new Lean theorem, prime density input, semiprime coverage theorem, generic scalar-query lower bound, or full factorization result is claimed. No repository edits or builds were made.
