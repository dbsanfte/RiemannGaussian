# Integration self-audit and primary-source pins

26 October 2026. Author self-audit, not independent review. Scratch only.

## Boundary-coverage scope and constants

- Exact native M is `ceil(4*ceil(sqrt(kN))/H)+2`. Therefore
  `H(M+1)<=4sqrt(kN)+4H+4`. For T=Q/P>=25k,
  `T-k-4sqrt(kT)>=4k`; multiplying by P>16H makes the remaining
  `4H+4` error harmless. Thus the stated threshold rigorously gives
  `Q-kP>H(M+1)` and excludes every original NONAXIS stationary
  certificate from [-M,M]. This does not exclude accidental modular
  hits or imply a controller's continuing branch on those inputs.

- The radial-scaling paragraph is now explicitly restricted to
  NONAXIS rows. Product admission alone does not admit scaled axes:
  the old catalogue stores only its four specified coefficient axes.
  The canonical carry and Fermat gap identities are exact. The
  `[k/4,k)` maximal-scale band is a coarse radial band, not a proof
  that the scaled point belongs to a Young-corner list.

- Fixed gamma in (0,1/2) gives the stated prime intervals, N between
  k^6/512 and k^6/128, and hence N>(k/3)^6. The least native 2*3^e
  above N^(1/6) is exactly k. The ratio lower bound
  `Q/(kP)>k^(1-2gamma)/4194304` diverges; P/H diverges as well.
  Both primes 11 mod12 give odd-part order (p-1)/2 coprime to H,
  so suitable CRT beta and q with large odd local orders EXIST.
  No cross-order coprimality or forced controller continuation is
  claimed. The source scalar-catalogue coverage itself needs neither.

- The prime-interval observation is an existence argument about
  actual semiprimes, not a sampled numerical example or claimed
  new hard-instance theorem. Its source bound proves a prime in
  each dyadic interval once the lower endpoint exceeds 8*10^9.

- The axis discussion counts ALL k canonical phases per horizontal
  sign. Four lambda=0 rows are not the full axes. The quoted
  `sqrt(P)` and k^(1+gamma/2) are costs of the existing tiled-factorial
  construction, not lower bounds on another residue supplier.

- Primitive fixed-phase uniqueness and the square-row count concern
  the WHOLE public colour domain. They do not show that the actual
  factor colour for a fixed N is absent from a correlated small bank.
  A root R in the square-row ansatz is conditional on R^2=N mod H;
  that branch is not silently supplied for every semiprime.

## Primary download pins

The inspected primary source is Bennett--Martin--O'Bryant--Rechnitzer,
*Explicit bounds for primes in arithmetic progressions*, arXiv:1802.00085,
Theorem1.2 and equations(1.10)-(1.12). Modulus12 has phi=4 and
`|theta(x;12,11)-x/4|<x/(840log x)` for x>=8*10^9. Hence the dyadic
increment is greater than `x/4-3x/(840log x)>0`.

- Download URL: https://arxiv.org/pdf/1802.00085
- Published author PDF: https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf
- Downloaded PDF: `/tmp/boundary-primes-ap.pdf`
- PDF SHA256: `e51f8b8f63486c2259efe076d367504f08dda0fe9e99dc35bf36de544ffc0601`
- Extracted text: `/tmp/boundary-primes-ap.txt`
- Text SHA256: `7b1a464bf90d262175fde611df0c2e51ffd8cbaf7101be823ffcda605b7a5323`
- Text theorem location: lines221-227 (Theorem1.2); constants lines197-219.

The PDF theorem, not only the abstract or a secondary citation, was read.
No computations of example primes or coverage tests were performed.

## Additional read-only check of native-boundary.md

The supplied row character identity agrees with the canonical carry:
`X^t Y^b Z^tau=beta^(a+bN+lambda)` with Z=q^-1.
The eight-product cleared identity has the correct parity signs: its
numerator translates are 1,XY,XZ,YZ and denominator translates
X,Y,Z,XYZ. The one-row endpoint quotient has the correct first-included
and first-excluded indices. Local epsilon orders count collisions
exactly over each hidden field, without a derivative/factorial assumption.

A boundary factor with explicit integer label D!=0 legitimately has
the old own-label proper-gcd/global-annihilator consumer. Literal D=0
must be omitted only from a SCREEN, not numerically divided from the
cleared identity. The report correctly states that distinction and
makes no boundary-coverage claim. Its soft-k endpoint enumeration
therefore does not conflict with the unacquired interior collision
ledger. This is an additional finite-algebra check, not an independent
review of the incidence enumerator or its source coverage proof.

## Axis completion clarification added after integration question

The tiling paragraph now distinguishes two interfaces. Restoring only
NONLITERAL leaves of a deleted row in the complete all-phase catalogue
multiplies by certified units: E=Hi0 and 0<|i-i0|<=2M<16H. Its predicates
are therefore unchanged, though literal scalar equality is not claimed.
Completing a smaller unit-tag/stationary-colour list to all k phases is
instead a licensed factoring OVERCOVER, not predicate equivalence. Every
added literal leaf is omitted in advance; other leaves have their own
nonzero short exponent labels. The exact interval tiling and its
soft sqrt(kM), or adaptive soft sqrt(P), costs refer to that specified
completed construction. They are method upper bounds, not impossibility
or complexity lower bounds for another phase/residue supplier.
