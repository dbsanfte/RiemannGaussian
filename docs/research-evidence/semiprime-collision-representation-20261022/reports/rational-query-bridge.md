# Rational-query bridge: exact orbit rearrangement and a paid chirp subprimitive

No near-linear native collision query is proved. This check separates a usable root-free fast transform from the precise mixed operator still missing.

## Fixed-array orbit matching does not follow merely by rearrangement

Use W=t(1+gamma X)/(X+gamma), rho_j(X)=X^j and the native corrected row Z_j from torus-frobenius.md. Applying rho_j gives

 rho_j(Z_j)=(rho_j W)^ell (rho_(j²) W)^a W^N.

Thus the row/seed collision is equivalent, in the WHOLE hidden local algebra, to

 B=W^N=rho_j(A_(j,i)),
 A_(j,i)=W^(m²i−ell) (rho_j W)^(−a).

The left array is fixed and paid, but the right input depends on both tag and long index. Therefore a paid all-j correlation separator for fixed arrays A,B does not directly apply. The exact additional theorem needed is acquisition of suitable correlations of this variable mixed-power family with B, with same-leaf conjugate pairing retained. Computing A_(j,i) explicitly per pair is not within budget.

For R(x)=(1+gamma x)/(x+gamma), the multiplication defect is explicitly

 R(x)R(y)/R(xy)
 =((1+gamma x)(1+gamma y)(xy+gamma))/((x+gamma)(y+gamma)(1+gamma xy)).

This is a rational coboundary and obeys the exact cocycle identity delta(x,y)delta(xy,z)=delta(y,z)delta(x,yz). Binary powering can use this identity, but the native products still require differing a,j and carried exponent ell. No identity here makes their corrections independent of j. Initial W denominators are units; denominators introduced by arbitrary displayed rational decompositions must still be checked or carried projectively.

There is also no legitimate shortcut by differentiating equality modulo X^m−1: differentiation does not descend to this etale algebra when gcd(m,N)=1, since d(X^m−1)/dX=mX^(m−1) is a unit. Derivatives of equal residue classes can differ. Hence logarithmic derivatives cannot turn the whole-algebra power equality into a free bounded-degree rational equality.

## A genuinely paid nonperiodic quadratic transform

For ANY public unit u, any f_0,...,f_(s−1), and 0<=j<r, the sum

 T_j=sum_k f_k u^(jk)
 =u^(−binom(j,2)) sum_k [f_k u^(−binom(k,2))] u^(binom(j+k,2))

is obtained by one ordinary convolution, reversing the first coefficient sequence. Thus all r+s-size bilinear/chirp sums cost soft O(r+s) scalar ring work, with no root of unity, square-root choice, or division by 2. Chirps with additional separate quadratic row/column phases are equally paid. Power tables use recurrences and all exponent sizes remain logarithmic in polynomially bounded lengths. This is the algebraic Bluestein/chirp-z mechanism and is a concrete available subprimitive for a future native separation; high-order gamma by itself does not preclude fast quadratic transforms.

The actual native data are not yet such a bilinear kernel. Writing h=j^(−1) in [0,m),

 a=N h²−m A_h,  A_h=floor(N h²/m),

retains the exact gamma correction gamma^(−m A_h k²) in a trial phase gamma^(a k²). Reindexing the finite quadratic phase by j is valid modulo m, but replacing gamma^(m A_h k²) by 1 is invalid. Row-dependent changes of variables modulo m also create k-dependent quotient carries. A proof that these exact carried kernels have a bounded number of separable/chirp pieces would enable the paid convolution above; no such decomposition has been derived. Arbitrary table reindexing alone does not pay the mixed power family A_(j,i).

## What finite Weil identities actually provide

Gurevich–Hadani–Howe, *Quadratic reciprocity and the sign of the Gauss sum via the finite Weil representation*, IMRN 2010, https://arxiv.org/abs/0808.2447, author PDF https://people.math.wisc.edu/~sgurevich/QR-IMRN.pdf, §2.2 and §3.1, constructs the representation using a faithful additive character psi:Z/mZ→C*, and the DFT F(f)(y)=sum_x psi(yx)f(x). Its periodicity and F²(f)(y)=m f(−y) are part of the actual algebra. The local native gamma has order >16m², so gamma^m!=1 and x↦gamma^x is not that additive character. The theorem cannot simply be specialized by replacing psi with gamma. Formal X^m=1 does give a legitimate cyclic phase in A, but m scalar outputs then become m A-valued outputs unless a separate contraction/compression is proved. This is a carrier charge, not a prohibition against the scalar convolution above.

Primary chirp source: Bluestein, *A linear filtering approach to the computation of discrete Fourier transform*, IEEE Transactions on Audio and Electroacoustics 18(4), 451–455 (1970), https://doi.org/10.1109/TAU.1970.1162132. The displayed binomial identity proves the required finite-ring version directly and avoids importing analytic convergence or a unit-circle assumption.

Weil PDF SHA256: 72cfb031d11f68e10e315e5013ecdf7d9c59e42358a6ce4b56c9b861ed300782. No quantum-dilogarithm claim is made; that route already has its separate cyclic-reciprocity audit in the repository.
