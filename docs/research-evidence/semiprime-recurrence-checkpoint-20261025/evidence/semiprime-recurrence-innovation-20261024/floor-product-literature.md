# Floor products, carries, and exact modular evaluation

2026-10-24. Repository read only. Input audited: `/tmp/semiprime-covering-lift-20261023/shared-affine-factorial.md`, SHA256 `5db88f386e78d69e60861ee96471ea66896fc94e1e275c782c5d68b319f2ae57`.

Outcome: no primary algorithm identified that acquires the varying-row carry correction in soft m aggregate work, or below the existing soft(m^1.5) sufficient factorial cover. There is an exact soft(a+m) algorithm for a *single complete rectangle* avoiding its am leaves; it does not provide a shared all-row algorithm. This distinction matters when testing Euclidean recurrences.

## Primary literature examined

- Pieter Moree, *Numerical semigroups, cyclotomic polynomials and Bernoulli numbers*, American Mathematical Monthly 121 (2014), 890–902, [author-hosted primary preprint](https://archive.mpim-bonn.mpg.de/id/eprint/3107/1/preprint_2013_45.pdf), [arXiv](https://arxiv.org/abs/1308.3972). Section 5 gives the two-generator Frobenius number, genus and gap generating function. These acquire sums/moments of gap exponents, rather than the polynomial whose roots are the gap integers. They do not evaluate the shifted gap product modulo N.
- Alexander Barvinok and Kevin Woods, *Short rational generating functions for lattice point problems*, JAMS 16 (2003), [primary preprint](https://arxiv.org/abs/math/0211146), [PDF](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Barvinok/0211146.pdf). For fixed ambient dimension, projected lattice-point sets admit polynomial-input-size short rational generating functions. Boolean operations and counting are available in that encoding. The output is additive monomial encoding, not a product of affine evaluations. No multiplicative norm oracle over Z/N is furnished.
- Shahen Alexanian and Alexey Kuznetsov, *On the Barnes double gamma function*, 2022, [primary full text](https://arxiv.org/html/2208.13876). Section 3 constructs a numerical complex evaluator from gamma/log-gamma values and an asymptotically corrected truncated product. Theorem 1 assumes complex z and |arg(tau)|<pi and gives an asymptotic expansion for fixed z,tau as truncation tends to infinity. It supplies neither modular ring arithmetic nor a uniform exact residue complexity for growing rational arguments. Rational-period multiplication identities still invoke Barnes values. They cannot be counted as acquired modular endpoint values.
- V. S. Adamchik, *Symbolic and numeric computations of the Barnes function*, Computer Physics Communications 157 (2004), [primary publisher](https://doi.org/10.1016/S0010-4655(03)00498-3). Its stated algorithmic setting is high-precision numerical Barnes gamma computation; no exact composite-modulus floor-product theorem was identified.
- Bostan–Gaudry–Schost, *Linear recurrences with polynomial coefficients and application to integer factorization and Cartier-Manin operator*, SIAM J. Comput. 36 (2007), [primary article](https://doi.org/10.1137/S0097539704443793). The ordinary factorial engine has square-root length complexity, and the ring-general product-tree/multipoint route pays logarithmic overhead. This handles acquired affine intervals, not implicitly compressed two-dimensional carry masks for free.

Searches also included Euclidean products, products along Beatty sequences, Sylvester gap products, and modular multiple-gamma algorithms. No applicable exact modular floor-product theorem was located. This is not an exhaustive-literature or impossibility claim.

## Exact structural identification of the carry mask

Let a,m be coprime positive integers, L=am, and
  A={a h+m k: 0≤h<m, 0≤k<a}.
Every residue r mod L occurs once in A, with representative either r or r+L. Its representative is r+L exactly when r is a positive gap of the numerical semigroup S=<a,m>.

Proof: if r is representable nonnegatively and r<L, any representation r=ah+mk must already have h<m and k<a, hence is the unique rectangle representative. If r is a gap, the unique representative is not r, so must be r+L. The maximum rectangle value is below 2L, proving the dichotomy.

Thus the source epsilon mask has gap set G and cardinality g=(a-1)(m-1)/2. With x=c'/m (m is a certified unit), define
  H_(a,m)(X)=prod_(r in G)(X+r).
Then the exact polynomial identity is
  R_(a,m)(X) H_(a,m)(X) = B_L(X) H_(a,m)(X+L),
  R_(a,m)(X)=prod_(h<m,k<a)(X+ah+mk),
  B_L(X)=prod_(r<L)(X+r).
The H factor has degree g, generically Theta(am), not O(a+m). Its additive gap generating function is
  sum_(r in G)z^r = 1/(1-z) - (1-z^L)/((1-z^a)(1-z^m)).
This short rational expression does not itself acquire H(x), H(x+L), or their quotient. Replacing additive counting by a multiplicative valuation is an additional algorithmic step requiring proof and cost.

## A completely paid single-rectangle acquisition

For a fixed scalar x, construct
  U(T)=prod_(h=0)^(m-1)(T+x+ah), degree m.
Evaluate U at T=mk for k=0,...,a-1, then multiply the a values. Product-tree construction plus monic multipoint evaluation costs soft(m+a) residue operations and soft(m+a) storage, avoids the am leaves, and uses no evaluation-value or node-difference inverse. Equivalently this is a resultant of degree-m and degree-a explicit polynomials, but MPE is the simpler unit-safe implementation.

The actual source scale c'+m(ah+mk) contributes known factor m^(am). Translation of h,k interval endpoints changes x only; endpoint exponents have O(log N) bits here. General rectangle widths u,v cost soft(u+v), with degree u and v explicitly paid. This is an exact algorithm, not Barnes notation.

If the purpose is just the *correction ratio* and B_L(x) is a unit, acquiring B_L(x) via the ordinary square-root factorial engine and dividing gives
  H(x+L)/H(x)=R(x)/B_L(x)
for cost soft(a+m+sqrt(am)). This does not separately acquire either gap polynomial value. The division is performed only after gcd(B_L(x),N)=1. A proper gcd already factors N. A gcd equal to N requires a paid descent; the source bounds ensure the corresponding unscaled integer leaves are nonzero and smaller than N, so descent reaches proper factors. This gcd branch uses the source's leaf envelope, not a universal promise about arbitrary x.

Across the m-1 source rows, a_j=O(m), these exact per-row algorithms cost soft(m²) aggregate work. The menu width is O(m); each whole row menu rectangle likewise costs soft m, still soft m² across rows. Splitting into Euclidean rectangles must charge every emitted endpoint and the sum of their widths/degrees; logarithmically many geometric descriptions alone do not imply a logarithmic modular product cost. No literature theorem found removes this varying-row aggregate.

## What would constitute a genuine improvement

A useful new algorithm must take the O(m) varying row metadata and acquire the product of their scalar gap corrections, or a sufficient covered gcd support, while charging the actual endpoint/degree work. A recurrence that reduces a,m but leaves an uninitialized H value at the terminal boundary is incomplete. Formal double gamma identities, short additive generating functions, and unit division after an unacquired denominator do not meet this condition. Existing soft(m^1.5) clipped factorial coverage remains the strongest established sufficient route in the supplied source.
