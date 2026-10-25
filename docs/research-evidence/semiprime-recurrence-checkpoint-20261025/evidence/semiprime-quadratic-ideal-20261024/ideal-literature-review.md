# Independent review of the native norm-fiber ideal

24 October 2026. **PASS. No source corrections requested.** Exact source reviewed: `/tmp/semiprime-quadratic-ideal-20261024/ideal-literature.md`, SHA256 `90f760d067f9de61a2950289c4f8aceba013cba521a2e4078053c2c2916ef77b`. No audited source or repository file was changed.

## Factor-or-target separation

The saturated-pair lemma uses the actual native hypotheses correctly. At the unique nonsplit side, saturated Norm(V_j-V_h) implies whole-element equality. Norm comparison gives beta^[2(delta_j-delta_h)]=1; its exponent has absolute value at most8H, below the local order>16H, so the integer deltas are equal. Their unit norms then agree globally. At the split side, equality of either coordinate of two unit pairs with the same product forces equality of the other. Thus saturation would mean an actual global duplicate. The exact sorting stage has already removed those, so a retained pair's nonunit norm gcd is always proper.

The execution is genuinely soft J, not a disguised all-pairs scan. A monic product tree, derivative and monic multipoint evaluation acquire every F'(V_j) without presuming separation. If all derivative norms are units, every pair difference is a unit in B. Otherwise only ONE bad row is scanned at its O(J) actual pair costs; multiplicativity guarantees a bad pair and the lemma guarantees a proper factor. The scalar gcd work and all rank-two coordinates are included. Exact global duplicate deletion preserves actual target masks and original labels; delta-only deletion is never used.

## Exact ideal, not just a vanishing overcover

Distinct norm nodes are certified separated by the same short beta margin. Dense G and all F_d, unit derivative values and the CRT selector constants are acquired within soft J. The shared complement construction is an arithmetic circuit of O(J) gates, not M separately expanded degree-M selector vectors. The source explicitly limits that claim to circuits and charges the dense coefficient data it actually acquires.

The ideal identity survives both local types and the composite ring. After the faithfully flat free quadratic extension, the invertible change u=X+tauY, v=X-tauY sends the norm equation to uv=n_d. The two component equations become F_d(u) and bar(F_d)(v). With every V_j*bar(V_j)=n_d,

    bar(F_d)(n_d/u)=(-1)^r (product_j bar(V_j))*u^(-r)*F_d(u)

is exact. Its multiplier is a unit, and the unit constant coefficient of F_d makes u invertible in its quotient. Therefore the fiber quotient is B[u]/F_d, which is the product of its actual r unit-separated root copies of B. The recovered X,Y coordinates are exactly x_j,y_j. Faithfully flat descent gives the stated true point ideal over R, with no extra off-diagonal points. Unit difference norms also directly imply comaximal coordinate ideals. This is a structural proof, not computation in hidden fields.

The circuit degree ledger is correct: G(X²-DY²) has degree2M and unit leading X^(2M) coefficient; the other generators have the stated degree upper bound. No expanded nearlinear bivariate basis or free elimination is asserted.

## Public modulus refinement and native fiber bound

For N=1 mod4, factoring the acquired Jacobi-minus-one integer gives a public prime ell with negative Jacobi sign. Removing the other factors is legitimate by multiplicativity; the chosen negative fundamental discriminants preserve that sign, including D=-8 for ell=2. For N=3 mod4, D=-4 is correct. Discovery and factoring stay inside the predecessor's accepted soft-N^(5/32) scan budget and its explicit finite failed-scan convention; no new least-nonresidue assumption is inserted.

The q supply is paid and uniform. A=max(3,ceil(r/(2c))) is public; two Bertrand intervals provide a prime at most4A different from ell, even if the first available prime equals ell. The sieve has soft A cost. Then k=2cq is even, c-divisible, at least r and O(r+c)=Theta(r), with its factorization known. The source reruns preparation and all seed guards at this ACTUAL k. It imports no order certificate for a different modulus.

The claimed prime-power structure follows: at most two DISTINCT odd primes each to exponent one, and v2(k) in{1,3,4}. The exact congruence

    N^(-1)*delta_j=(j^(-1)-1)²-1 modk

has the correct signs. An exact delta gives at most two roots per odd prime and at most four modulo2^e for these e. CRT therefore bounds every raw delta fiber by16, with injectivity of j->j^(-1)-1 retaining the tag count. Consequently M>=phi(k)/16. Since the two smallest possible distinct odd primes are3 and5, phi(k)/k>=4/15, so M>=k/60. Global target deduplication cannot remove a distinct-delta fiber, because equal targets force equal deltas. These are actual full-family cardinality bounds for the NEW modulus, not bounds for arbitrary earlier conductor multiples or an algorithmic lower bound.

## Explicit seventeen-coefficient interpolation

Padding each F_d with ZERO coefficients through degree16 does not add roots or alter its true fiber degree. Interpolating the seventeen B-valued coefficient functions at n_d uses only the acquired unit denominators, costs soft M per fixed coefficient, and gives actual arrays C_a(T) of degree<M. At a node the result is exactly its original F_d; varying leading fiber degrees cause no pivot division. Expanding only (X+tauY)^a for a<=16 has constant cost per T coefficient. Thus the actual auxiliary-coordinate ideal, dense in T and bounded-width in X,Y, has O(M) coefficients and is acquired in soft k.

Substituting T=X²-DY² is a different operation and can have O(M²) coefficient slots; that expansion is explicitly not claimed free. The norm projection still has degreeM=Theta(k), and the bounded fiber width alone supplies no balanced original-plane basis or terminal saving.

## Query, recovery, and primary theorem scopes

The norm-coordinate overcover is safe independently of exact point incidence. Its leaf is the original scalar condition beta^[2(E-Hi)]=1, so a proper gcd factors and saturation yields the original beta leaf after odd-order square removal. Labels and bounded i are retained before the original factor-sum decoder. The complementary plus factor is a unit in the odd beta subgroup. This is precisely the old scalar norm projection, with soft(M+sqrt(ML)) completion, not a new soft-k long query. Exact point incidence still needs the other component equations at the SAME index.

I checked the cached primary theorem statements and PDF hashes against the ledger. Jeannerod--Neiger--Schost--Villard Theorem1.3 receives the explicit field interpolation matrix and standard Jordan data; its soft(m^(omega-1)*sigma) scale, arbitrary shifts and input-size qualifications are represented correctly. At m~sqrt J the displayed substitution has soft J^((omega+1)/2) guarantee and an explicit Jm input. van der Hoeven--Larrieu's generic two-polynomial hypotheses, normal dominant-diagonal degree sequence and nonzero leading Y coefficient are not supplied by target separation. Their Theorem20 indeed costs O(R(m²)*n*log n), while their concise reduction/multiplication bounds assume the actual ideal input. Schost--St-Pierre2024 Theorem1.4 assumes a domain, fraction field, GOOD maximal ideal and an already supplied reduced basis modulo it. The cached later m-adic manuscript is randomized over a domain/fraction field. Neither initializes the required basis over unknown factors of R or acquires a long common-index seed product.

Verified PDF pins: interpolation `ab2a405bb5f7e86b0efd405ad614f04eb7c0a76da08fef48826dbea81b29e546`; generic ideals `c5d41a8624d882c4180ccd757219035b67216e3d849d8c02269bf9cbc99c1b89`; Newton2024 `f34f1374716e29a8ce8cda4f33306b80f3bc7850c582efdca62d407983184907`; m-adic manuscript `a6daf5998c6d9bc2012e53a4145513eef033026c49d0c9e30dafa42574f7486a`.

The report does not assume a torus-order supplier. The separately investigated supplier can strengthen the input later, but it is not needed for these separation, norm-fiber ideal or modulus proofs. The fixed Cayley repair likewise remains distinct from a finite-field large-order guarantee. All acquisition advances and the unchanged long-query scope pass at the exact reviewed bytes.
