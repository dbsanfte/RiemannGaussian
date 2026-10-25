# Direct geometric gcd: acquired pivots, bounded native normalization, and the remaining remainder

Status: constructive interfaces and a fully initialized direct-remainder algorithm; no faster terminal query. Arithmetic costs are soft-O in operations over R=Z/NZ, with ordinary logarithmic bit factors suppressed. Here B=R[tau]/(tau²-D) is the acquired quadratic étale algebra, 2D is a unit, and exactly one unknown prime side is a field (Jacobi(D,N)=-1). F=product_j(X-V_j) is acquired, monic of degree J, and its unit roots are pairwise unit-separated in B. The actual geometric seed q has q^d-1 units for 1<=d<=C=16k²; the query interval length L is O(k²) below this guard. Native bounded witnesses and the original saturated-leaf decoder remain the consumer. These statements do not apply an arbitrary auxiliary coefficient to that decoder.

## 1. A zero-safe coefficient primitive, not a free implicit gcd

For a=x+y tau compute n=x²-Dy² and g=gcd(n,N).

* g=1 certifies the inverse bar(a)/n.
* 1<g<N returns a factor.
* g=N implies a=0 on the nonsplit field side, hence both x and y vanish at that prime. If a is not globally zero, gcd(x,y,N) is a proper factor. If x=y=0 in R, a is globally zero.

Thus each acquired B coefficient is factor-or-unit-or-global-zero. This includes a saturated norm whose split side vanishes in just one component: its coordinate gcd still finds the nonsplit prime unless the coefficient is globally zero. Consequently ordinary Euclid or half-gcd on two acquired polynomials can normalize every nonzero leading coefficient, or stop with a factor. No division by an untested nonunit is used. With standard guarded fast half-gcd the acquired degree-J problem costs soft-O(J), including soft-O(J) coefficient-level unit/zero tests, each at logarithmic bit cost. There can be Theta(J) leading-pivot tests; logarithmic recursion depth is not a bound on their number. Degree scans are charged to the coefficient arrays actually produced: store each polynomial’s degree, scan a newly formed or truncated array once to find its first nonzero coefficient, and reuse that degree. In the usual half-gcd recursion, the sums of recursive size parameters at each depth are O(J), while multiplication and correction work is soft-linear at those sizes. Thus all such scans and normalization tests total soft-O(J), within the standard soft-linear arithmetic ledger. Ordinary Euclid is lawful too, but is not assigned this fast complexity bound. This solves the coefficient-ring issue; it supplies none of the coefficients of P_L mod F.

If this process produces a monic gcd G of F and P_L mod F, degree zero certifies no collision in every local component. If its degree is positive, evaluate G at all V_j by monic multipoint evaluation. Some value is nonunit, since over at least one local field a root of G is an original root of F. Apply the primitive above: a proper factor ends the computation, while a globally zero value selects an original row with a collision on the nonsplit side. A one-row geometric product and interval localization costs soft-O(sqrt L), followed by the original leaf decoder. A globally zero G(V_j) does not identify a common geometric index across the two prime sides; that index must still be localized. The same procedure applies to row restrictions and interval restrictions, retaining the original labels.

## 2. One initialized direct remainder algorithm without native point values

Set A=B[X]/(F), let x be the residue of X, and choose s near sqrt L. Acquire the actual scalar polynomial B_s(Y)=product_(0<=i<s)(Y-q^i), costing soft-O(s). Write L=a s+d. The full blocks in A are

    product_(0<=i<s)(x-q^(sg+i)) = q^(s²g) B_s(q^(-sg)x).

Acquire the a actual arguments q^(-sg)x. Monic multipoint evaluation of B_s at them in A costs soft-O(s+a) A-operations; multiply those block values, the known q powers, and the analogous actual d-factor tail. Every polynomial division in the evaluation tree has a monic divisor. Its coefficient ring A may have zero-divisors, which cause no division. Arithmetic in A costs soft-O(J) B-operations using monic reduction by the acquired F. Thus

    cost = soft-O(s + J(s+L/s)) = soft-O(J sqrt L).

This computes the complete degree-<J remainder and then permits Section 1. All starts and the tail are paid. At J~k,L~k² it costs soft-O(k²), so this candidate is worse than the existing query. Binary splitting the implicit product does not turn an A-operation into a base-ring operation: its states remain degree-J residues. No nearlinear bound follows merely from asking only whether their product has a zero.

For comparison, a lawful better remainder acquisition explicitly uses native values. With the same L=a s+d,

    P_L(V_j)=q^[s²a(a-1)/2+as d]
             product_(0<=g<a) B_s(q^(-sg)V_j) B_d(q^(-as)V_j).

Acquire all J a mixed arguments, perform scalar polynomial multipoint evaluation, multiply per row, then interpolate the unique degree-<J remainder at the V_j. Interpolation uses the certified units F'(V_j), so it remains lawful over B. Its cost is soft-O(s+JL/s+J), optimized at soft-O(J+sqrt(JL)). This is the existing k^1.5 scale, and explicitly acquires the native values. Neither presentation supplies a scalar-only shortcut.

## 3. An actual constant-width native q-shift normalization

This section uses the acquired native representation

    V_j=beta^(N+delta_j) W^(T_j),  q=(beta W)^H, H=k²,
    Norm(V_j)=beta^[2(N+delta_j)], delta_j in [-3H,H].

The controlled modulus construction gives at most 16 tags for each exact integer delta. Group tags by r=delta mod H and put t_j=(delta_j-r)/H, A_j=V_j q^(-t_j). Each group contains at most five delta values, hence at most 80 tags, and all A_j in it have the same unit norm beta^[2(N+r)]. Actual powers have logarithmic exponents; all pair tests within these constant-size groups cost soft-O(J).

For two such anchors, test Norm(A_j-A_h). A proper gcd factors. If its gcd is N, equality holds on the nonsplit side. On the split side, equality in either coordinate plus equality of the common unit norm forces equality in the other coordinate. Hence either a coordinate gcd gives a proper factor, or A_j=A_h globally. This is also an immediate application of Section 1. Group global equal anchors and retain their actual shift labels. After global target deduplication an anchor has at most five original shifts, with span at most four.

For one anchor class, the union of original collisions is exactly

    A=q^n,  n in union_t [-t,L-1-t].

If L>4 the union is one interval [-t_max,L-1-t_min], of length at most L+4; a known q-power makes it an ordinary geometric query. If an interval restriction is shorter, retain the at most five actual intervals and merge only overlaps, rather than filling holes. For each located n choose a stored actual shift t whose interval contains it, returning the original row and i=n+t. This preserves recovery. It does not recover an unknown local q-logarithm, or detect all possible long local q-shifts. Since each anchor removes at most five rows, this normalization alone leaves at least J/5 anchors and gives no query exponent saving.

## 4. Primary q-dispersion results require the missing orbit information

Sergei Abramov, *Rational Solutions of First Order Linear q-Difference Systems*, FPSAC 1999, Section 1 and Section 2.1: [primary PDF](https://fpsac-archive.github.io/FPSAC99/ARTICLES/abramov.pdf). The setup is a computable characteristic-zero field K, q not a root of unity, and a transcendental variable x. In addition K must be **q-suitable**: given p, an algorithm returns every nonnegative integer n with p(q^n)=0. Algorithm qUD first obtains the largest such index from Res_x(A(x),B(q^n x)); it then iterates downward through that index, doing gcds and constructing shifted factors. No nearlinear bound independent of this dispersion or of the resulting degrees is asserted. On A=F and B=X-1, the q-suitability call is precisely the desired root-on-orbit acquisition. It cannot be imported as an oracle.

William Y. C. Chen, Peter Paule, Husam L. Saad, *Converging to Gosper's Algorithm*, Advances in Applied Mathematics 41 (2008), 351–364: [published primary PDF](https://www3.risc.jku.at/publications/download/risc_3804/PublishedVersion.pdf), [author preprint](https://arxiv.org/pdf/0711.3386). Theorem 2.1 stabilizes a gcd of growing shifted products after k_0+1, where k_0 is the dispersion of two explicitly supplied characteristic-zero polynomials; the introduction computes dispersion via integer roots of a resultant. This is an additive-shift theorem in this paper, not a nearlinear finite-ring q-Pochhammer gcd theorem. Its convergence premise does not acquire native multiplicative orbit labels.

Over our finite algebra q has finite order locally. Whenever a root lies on its orbit, unrestricted nonnegative solution indices recur periodically; the characteristic-zero maximal-dispersion argument is inapplicable. The certified unit differences give distinct points in the bounded window, not an algorithm finding which native roots belong to that window. A coprime identity for formal transcendental q also cannot be reduced into a proof of finite-modulus coprimality: specialization can create precisely the local collision being sought.

Erich Kaltofen, *Greatest Common Divisors of Polynomials Given by Straight-Line Programs*, JACM 35 (1988), 231–264: [primary author PDF](https://users.cs.duke.edu/~elk27/bibliography/88/Ka88_jacm.pdf). The randomized polynomial-time theorem uses usual coefficient fields, controllable failure probability, and input degrees as **unary** parameters. It provides no deterministic soft-O(circuit size+J) bound independent of degree L, and no automatic replacement of the finite étale pivot checks above. Therefore an implicit product circuit plus this theorem is not the desired query algorithm.

## 5. Exact remaining contract

A sufficient new primitive would acquire either P_L mod F, or a guarded monic gcd with F and a restriction witness, in soft-O(J+sqrt L) without materializing J L/s values or performing sqrt L degree-J algebra operations. The present report supplies safe Euclidean pivots, an original-row consumer, and a constant-width native normalization. It does not supply that primitive. The covered original family and its soft-O(J+sqrt(JL)) completion remain intact; no new smaller family replaces coverage.

## Cached primary pins

The files below are in `sources/` beside this report, with extracted text for inspection.

* `abramov-fpsac1999.pdf`: SHA256 `af8f32f0a8325c86992a47f058efa8f2a2a73c91742fd2e64582aefbf666c0e0`.
* `chen-paule-saad-2008.pdf`: SHA256 `f307722e204ce34795b621d710c3fcb493f60de010318429fb91e92ec2e7fd5d`.
* `chen-paule-saad-arxiv.pdf`: SHA256 `63e97424e583062c3025de2da0973f1d565db603cc1ff956a27c14cda5a52582`.
* `kaltofen-duke-1988.pdf`: SHA256 `36f8c6e9e1c184ea9d6dd2270aa24843ebbd26c78881c7e69b69b75904d15731`.
