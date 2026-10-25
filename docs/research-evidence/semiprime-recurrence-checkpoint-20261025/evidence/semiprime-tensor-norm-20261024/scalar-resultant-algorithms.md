# Structured scalar tensor norm: generator adaptation and a two-pivot factor branch

2026-10-24. Scratch only; no repository edits or numerical examples. Target inputs are explicit F of degree J and two explicitly acquired geometric-root polynomials A_s,B_t, with J,s,t~m. The scalar is
  E=Norm_(R[X,Y]/(A_s(X),B_t(Y))/R)(F(XY)), R=Z/N.
All small q-differences are certified units. This pass gives a concrete, initialized early-pivot factor branch and tests the simplest secondary-generator closure. It obtains no guaranteed soft-m complete norm or restriction-stable factor query; the safe whole-query fallback remains soft(J+sqrt(Jst)). No general lower bound is claimed.

## Primary algorithms actually adapted

**Hyun–Lebreton–Schost, Algorithms for Structured Linear Systems Solving and Their Implementation, ISSAC 2017.** [Primary author PDF](https://cs.uwaterloo.ca/~eschost/publications/structured.pdf), [DOI](https://doi.org/10.1145/3087604.3087659). Sections 2–3 take EXPLICIT displacement generators, reduce mosaic Toeplitz systems to Cauchy-like form, and maintain generators through Schur complements. Divide-and-conquer costs quasi-linear matrix size for fixed displacement rank, over a FIELD with generic rank profile. Leading minors are tested; generic regularization is not a deterministic promise of unit pivots on our composite/split coefficient algebra. Geometric Cauchy node sequences accelerate matrix products by constants/logarithms; they do not replace a generator entry by its short circuit at unit cost. This is the strongest directly relevant concrete generator implementation examined.

**Emiris–Canny, Efficient Incremental Algorithms for the Sparse Resultant and the Mixed Volume, JSC 20 (1995).** [Primary author PDF](https://people.eecs.berkeley.edu/~jfc/papers/95/cejsc95.pdf), [publisher](https://doi.org/10.1006/jsco.1995.1041). The algorithm constructs coefficient matrices whose determinants are multiples of the sparse resultant and supplies determinant-only formulae for appropriate multigraded systems. Matrix size and work are charged through supports/mixed volumes, not the count of input polynomial expressions. The specific supports below have quadratic resultant degree even though their coefficient lists are linear-size. This source does not give a small scalar-only tensor norm algorithm.

The already-reviewed geometric-root scalar product algorithm is used ONLY for degree-one/four pivot norm screening below, with its actual fixed degree. No explicit modular-composition theorem is invoked as an implicit remainder oracle.

Primary PDFs cached under `sources/`: structured.pdf SHA256 `9834268a83b91fd33ffa92bfcd3e3aeb3946a573f39051ffce6660a7c6805ef7`; cejsc95.pdf SHA256 `9ad39a8b1706be441bcbfd3463a67d762e6cb483d320b9b1bf4b640ff0972dfd`.

## Actual displacement-generator adaptation

Put Q=q^s, S=R[Y]/B_t(Y). The inner resultant is the determinant of the Sylvester matrix
  M(Y)=Sylv_X(A_s(X),F(XY)), size n=s+J,
with entries in S. Its two Toeplitz column blocks give constant mosaic displacement rank (at most three in the one-block-row/two-block-column convention). Its generators are acquired from A_s coefficients and entries f_k Y^k. They have an O(s+J) MONOMIAL/DENSE-SCALAR description, with no st table input.

This is a genuine small generator input, but the source algorithm's base operation is an operation in S. S has rank t and is completely split at the acquired geometric roots: by unit q-differences, it is isomorphic to a product of t copies of R. Thus even if N were prime, S would generally not be a field. Rank profile can differ between its components. A nonunit S pivot cannot be inverted merely because its coefficient list is nonzero.

Expanding each of O(n) constant-rank generator entries as an arbitrary S element costs O(nt) scalars; ordinary multiplication/inversion in S costs soft t, not O(1). With expanded generators, a fixed-rank quasi-linear structured algorithm has an optimistic soft(nt)=soft m² scalar ledger, before solving field/rank-profile applicability. That is already worse than the native blocking fallback.

The geometric Cauchy transformation itself is lawful over R: choose disjoint q-power node sequences within a length O(n) range so their cross-differences are certified units. However multiplying a monomial generator column (f_0,f_1Y,...,f_JY^J) by the resulting Vandermonde produces entries of the form F(q^a Y), or truncated/scaled variants. There are O(n) such entries, each with degree J in Y. They can still be described as shifted copies of one F, but the source algorithm does not maintain that secondary description through arbitrary Schur complements. Expanding it pays nJ coefficients. This is exactly the additional closure statement a successful scalar adaptation must prove.

A norm guard is legitimate: for an acquired pivot p in S, Norm_(S/R)(p) being a unit implies p is a unit by the adjugate identity. A proper scalar gcd of its norm factors N. A saturated norm says some geometric component vanishes at EACH prime, possibly at different components; it supplies neither an inverse nor an original native collision leaf. Generic structured regularization cannot be used to erase this case without a paid proof.

## Sparse mixed resultant parameters on this exact object

The three supports of A_s(X),B_t(Y),F(XY) are horizontal, vertical and diagonal segments of lengths s,t,J. Their pairwise normalized mixed volumes are
  MV(A_s,B_t)=st,
  MV(A_s,F(XY))=sJ,
  MV(B_t,F(XY))=tJ.
Hence the sparse resultant has coefficient-block degrees st in F, tJ in A_s and sJ in B_t: all quadratic at our scale. The scalar norm is monic degree st in the constant coefficient f_0 if the other coefficients are held fixed. Therefore a universal determinant formula whose entries are affine-linear in the ORIGINAL coefficients must have size at least st. This is only a parameter obstruction for that coefficient-linear matrix class, not an arithmetic lower bound or a restriction on nonlinear/recursive scalar algorithms.

Calling the F support diagonal does not change this mixed-volume accounting. A smaller matrix with nonlinear or rational entries remains possible, but constructing/evaluating those entries must be charged. The initial size-(s+J) Sylvester over rank-t S is one such compressed presentation; its coefficient-algebra dimension is exactly what must not be dropped.

## Tangible test: two actual Euclidean pivots and a paid factor branch

Choose the balanced split s=J=n>=3 and t=floor(L/n), retaining a final interval of length <n by actual monic evaluation. Native J~m and L~m² give n,t~m. Let
  A_n(X)=X^n+A1 X^(n-1)+A2 X^(n-2)+A3 X^(n-3)+...,
  F(X)=X^n+B1 X^(n-1)+B2 X^(n-2)+B3 X^(n-3)+....
Y is a certified unit in S. Scale the second operand to the monic polynomial
  G_Y(X)=Y^(-n)F(XY).
Its kth coefficient below the leading term is g_k=Bk Y^(-k). The first remainder is R=A_n-G_Y, with r_k=Ak-Bk Y^(-k). Its leading coefficient is
  r_1=A1-B1/Y=P1(Y)/Y,
  P1(Y)=A1 Y-B1.
For geometric A_n, A1=-(1-q^n)/(1-q) is a certified unit. This first nonconstant pivot is therefore only linear in Y and can be norm-screened cheaply.

Compute the next remainder G_Y mod R FORMALLY, assuming this first pivot is a unit. Its leading coefficient is
  [g_2 r_1²-r_3 r_1-g_1 r_2 r_1+r_2²]/r_1².
Multiplying the numerator by Y^4 gives the actually acquired quartic
  P2(Y)=(A2²-A1 A3)Y^4
       +B1(A3-A1 A2)Y^3
       +(B2 A1²+B1² A2-2A2 B2)Y²
       +A1(B3-B1 B2)Y
       +(B2²-B1 B3).
This derivation uses a constant number of scalar operations on six acquired coefficients. The leading coefficient does NOT require any generic-F assumption. Indeed, writing e_k for elementary symmetric functions of 1,q,...,q^(n-1),
  A2²-A1 A3=e_2²-e_1 e_3
    =q² (1-q^(n-1))(1-q^n)²(1-q^(n+1))
       /[(1-q)(1-q²)²(1-q³)].
This follows by direct q-binomial substitution, and all displayed denominators AND numerators are certified units under the native guard. Thus P2 is formally degree four with unit leading coefficient before any reduction modulo B_t. For t>4 this degree is not hidden by the outer modulus. At small t use the paid ordinary reduction instead.

This symbolically executes the first two pivots on the ACTUAL geometric A and arbitrary acquired native F. It disproves closure of the tested secondary class 'only linear Y denominators/geometric shifts at every step'. It does not disprove another compressed representation: the first two steps themselves still have O(n) bounded-degree descriptions. Constant displacement rank alone has supplied no theorem controlling the degrees/circuits of later secondary generators.

### Initialized adaptive factor branch

1. Acquire A1,A2,A3 (from the already paid A_n or the short q-binomial formula) and B1,B2,B3 from F. No root table or rank-t generator expansion is needed.
2. Acquire H1=prod_(b<t)P1(Q^b). Since A1 is a unit, this is one shifted geometric-root product times a known unit, costing soft sqrt t scalar work. Alternatively the ordinary fixed-degree geometric blocking proof gives the same bound.
3. If gcd(H1,N) is proper, return the factor. If the norm is a unit, the first S pivot is legally invertible. If gcd=N, record a degenerate pivot and return to the original safe query; do not invert or claim original-hit recovery.
4. On the unit branch, acquire H2=prod_(b<t)P2(Q^b). P2 has acquired constant degree four, so fixed-degree geometric blocking costs soft sqrt t, with no P2-value inverses. A proper gcd factors N. If the norm is a unit, the second pivot is legal as well, since its remaining denominator is a product of known units Y and r_1. A saturated norm again triggers safe fallback.

Total extra work is soft(n+sqrt t) including the already explicit input coefficients/metadata; it fits soft m. This is a real adaptive proper-factor operation, not a promised fast evaluation of E. It may find factors that ordinary endpoint acquisition would also find, but no native coverage theorem for these pivot norms has been established. A saturated P1/P2 norm is not an original beta equality and MUST NOT be sent to the original factor-sum decoder.

To continue elimination one could keep factored rational Y expressions, guard their norms and maintain exact determinant factors. This is a tangible next test, but every new pivot numerator, its norm and its S arithmetic remain to be acquired. No all-n closure bound or soft-m scalar result is claimed. Computing an S inverse in full coefficients is itself soft t; performing O(n) such operations without extra structure costs soft(nt).

## Native low-band roots: a paid normalization, not a pivot decoder

For Y_j=beta^(N+delta_j), write
  F(X)=beta^(nN) F0(X/beta^N),
where F0 has explicit roots beta^delta_j. Its top coefficients satisfy Bk=beta^(kN) Bk0. Thus the quartic above has the exact weighted homogeneity
  P2(Y)=beta^(4N) P20(Y/beta^N).
Removing the common beta^N scale is acquired in soft n and merely shifts the geometric outer node sequence by a known unit. The delta_j=O(m²) band does not turn their elementary symmetric sums into geometric powers or identify the scalar pivot roots as native targets. In particular P1 involves the SUM of original roots, not one retained row. Global vanishing of a pivot is therefore not licensed by the original beta annihilator decoder. Exact q-chain coincidences can be used if acquired, but are the previously recorded conditional branch and not supplied by the band alone.

## Restrictions, recovery and stopping point

The two-pivot branch can be repeated for row restrictions by acquiring their actual F coefficients, and for index subintervals by the known q-start scaling plus actual tail evaluation. If an interval is too short for this balanced split, direct MPE is already within its paid short bound. Every proper gcd is independently verified against N. Saturated or degenerate auxiliary pivots preserve the original problem and fall back to the initialized native product query, which retains original row/index labels for zero-safe descent and global-leaf recovery.

For the COMPLETE scalar-resultant target, a zero value at both fields can be expected under known coverage and is not itself a factor. Any successful new norm routine must support restrictions sufficiently to localize, or provide a separately proved decoder. Neither sparse resultant degree bounds nor small initial displacement generators supply that functionality by themselves.

Delivered: actual generator/input adaptation, a symbolic two-step closure test showing a unit-leading quartic, and a soft-m adaptive early-pivot factor branch with lawful degeneracy handling. The full native query still has the old soft m^1.5 fallback. The specific unresolved positive task is a secondary generator class closed under all necessary Schur complements, with TOTAL scalar arithmetic and restriction recovery charged, or a covered pivot subset that avoids full elimination. No general impossibility, numerical experiment, hidden field, free rank-t ring operation, or backend theorem is asserted.
