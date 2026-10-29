# Rectangle difference query: safe collapse, axis removal, and acquired scalar cost

26 October 2026. Bounded exact-algebra investigation; scratch only, no tests, numerical campaign, or repository edits. **Outcome:** rectangle pair edges collapse to O(k) canonical difference rows per cell, and their known canonical carry enlarges the shift interval only from[0,6k] to[0,6k+1]. More strongly, every guaranteed short edge has nonzero difference in BOTH coordinates. Omitting axis difference rows makes the public cell filter unnecessary for this new overset. The resulting complete scalar is acquired by the old monic geometric-product engine in soft O(k²), including localization and extraction. This is worse than the current query. The executed row-string attempt below does not amortize its starts; no improved full-query bound is claimed.

## 1. Exact collapse with the correct sign

Use the inherited N=P Q, P<=Q, N<=k^6, H=k², P,Q>16H, k>16, and the supplied beta,q=beta^H. For a unit colour j and dyadic B<=k let

    A=ceil(2H/B),
    S={(a,b):0<=a<A,0<=b<B, a*j²=bN modk}.

The authoritative dense-box coverage theorem supplies a true-colour cell with two distinct points u,v and physical index difference s=I_v-I_u in[0,6k]. Write w=v-u=(a,b), and lambda_w=[-aj-bN*jinv]_H. Since the phase is linear modulo H,

    lambda_v-lambda_u=lambda_w+H*c, c in{-1,0},
    E_v-E_u=E_w+H*c,
    beta^E_w=q^(s-c) modP.                         (1)

Thus the new clock index is n=s-c in[0,W], W=6k+1. With the equivalent epsilon=-c convention, n=s+epsilon. The product of ratio-edge factors is not asserted numerically equal to the new product: this is a COVERAGE-PRESERVING OVERSET with valid new leaves, not cancellation of pair multiplicities.

Every such w is in

    D={(a,b): |a|<A, |b|<B, a*j²=bN modk}.

For each of the 2B-1 possible b there is one a residue modulo k. Hence |D|<4AB/k+2B<=10k+4<12k. This is the exact constant-factor point bound that replaces O(k²) pair edges per cell by O(k) difference rows. It does not replace the O(k) colour/scale cells by one cell.

## 2. Remove axis differences; then discard the cell filter

The original filtered construction already makes all nonzero difference leaves nonliteral, including augmented rows that were not actual differences of two rectangle points. There is a stronger simple ledger for this new query.

For the actual true-colour pair, if Delta b=0 then Delta a=k*ell with nonzero integer ell, and

    |I_v-I_u|=|Delta a*P+lambda_v-lambda_u|/H
       > P/k-1 >16k-1 >6k.

This contradicts the guaranteed short gap. Therefore the guaranteed pair has b=Delta b!=0. Moreover a=0 is impossible for any nonzero lattice vector with |b|<B<=k: a=0 would force k|b because N is a unit modulo k. Thus a!=0 too. No stationarity density assumption or generic-root example is used.

Consequently define D* by the conditions of D and b!=0, and use ALL public cells, without applying A<=H/gcd(j-1,k). For every row in D* and every n in[0,W],

    E_w-Hn=bN+(a+lambda_w-Hn),
    |a+lambda_w-Hn| < H*(W+3) < N.                (2)

Here |a|<A<=2H, lambda_w<H, and N>256H² dominates H*(6k+4). Since b!=0, every exponent in(2) is NONZERO, for EVERY public cell and augmented row. This is the full public nonliteral-leaf guarantee; no unknown literal-edge mask remains.

For transposition, keep lambda_w and replace(a,b) by(b,a). The colour changes to N*jinv modk and the phase agrees. Since a!=0, its label satisfies

    E_transpose-Hn=aN+(b+lambda_w-Hn)!=0,

using |b|<k and the same bound. Thus transposes are also safe, and the guaranteed pair at Q has the SAME n as its original pair at P. Canonical carry c agrees because the endpoint phases are retained. The full product over cells, D* and transposes is therefore zero modulo BOTH primes; a scalar nonunit query would already suffice with the original cells alone.

For comparison, on the original FILTERED cells all axis difference factors can also be certified units directly. Write a=k*ell, lambda=k*r, 0<=r<k. Then E=k*h with h=ell+r in(-k,2k), and

    beta^E-q^n=unit*(1-(beta^k)^(kn-h)).

The filter implies kn-h!=0, and |kn-h|<6k²+2k<16H<=ord_local(beta^k). This is a proof of unit status, not a numerical product acquisition. The unfiltered D* formulation simply omits these axes entirely and uses the preceding actual-gap proof to preserve coverage.

## 3. Complete scalar and legal recovery

An explicit complete target with no optional divisions is

    Z=product_(all public cells and their transposes)
       product_(w in D*) product_(n=0..W)
          (beta^E_w-q^n).                         (3)

Keep each cell's original orientation and row metadata. Empty cells, including B=1 after axis removal, are skipped. Literal duplicate leaves may be retained; they affect multiplicity but not local zero/nonunit predicates. No numerical ratio separation or quadratic distinct-alphabet lower bound is inferred.

Equation(1) plus the actual dense-box coverage proves Z=0 modN for every prepared semiprime. Equation(2) proves EVERY leaf has a nonzero O(log N)-bit beta exponent E_w-Hn. A proper leaf gcd returns a factor. A saturated leaf gives a licensed short-annihilator input; charge T_ext=soft O(N^(31/192)) at most once. An augmented leaf need not reconstruct two points of the old rectangle or an old low-product catalogue leaf. Its public nonzero exponent is its OWN recovery certificate. The task is factoring, so this is sufficient; no reverse implication to an original physical edge is claimed.

For a prefix oracle, restrict the public cell list and/or n interval before forming(3). These restricted products need not retain global-zero coverage, but their scalar gcd/nonunit status can be queried without division. Binary searches on nonunit prefixes select a cell and n; after that materialize its O(k) differences and use a row-prefix search or scan to select a leaf. A zero-only bit without nonunit status is not silently used for this localization. Every selected augmented leaf still has the nonzero gap(2), independently of which prefix selected it.

## 4. Fully initialized algorithm and its actual bound

Materialize the D* lists for all cells by looping over b and the one a progression modulo k. There are O(k logk) descriptors, O(k) rows each, hence soft O(k²) total incidences. Canonical phases, beta powers and metadata use polylogarithmic bit work per row. Product trees form their monic root polynomials in soft O(k²). Keeping transposes changes only a constant factor.

One may combine every acquired root into one polynomial F of degree D_total=soft O(k²). The current division-free geometric-product engine on q^0,...,q^W then costs

    soft O(D_total+sqrt(D_total*(W+1)))=soft O(k²).  (4)

Alternatively each O(k)-degree cell at length O(k) costs soft O(k); summing cells gives the same bound. Repeated local nodes or nonunits do not license inversions and do not invalidate monic remainder evaluation. Scalar gcds and binary prefix localization add only logarithmic factors. The final T_ext is below soft k and therefore below(4). This is a complete acquired algorithm, not merely an implicit determinant, but it is slower than the current native soft k^(5/4) algorithm. The collapse alone does not improve the goal.

The point-count bound does not imply that all numerical nodes or all globally deduplicated leaves have that many distinct values. Conversely no unproved small global alphabet is used to reduce(4). A new amortized algorithm could avoid this materialization; (4) is not a lower bound for such algorithms.

## 5. Execute the geometric-row-string route

For fixed j,B and b!=0, take the least admissible a_b in(-A,A), then write the row progression a=a_b+k*t, 0<=t<L_b. Acquire its canonical phase lambda_b and x_b=beta^(a_b+bN+lambda_b). Exactly,

    R_j=beta^[k*(1-j)],
    c_b(t)=-floor((lambda_b-k*j*t)/H),
    x_(b,t)=x_b*R_j^t*q^[c_b(t)].                  (5)

For t>=0, 0<=c_b(t)<=t. Thus a collision at canonical index n is the collision of x_b R_j^t with q^(n-c_b(t)). This is an exact integer carry, including endpoints; setting c_b(t)=0 is not legal. The row-string target is

    product_(t=0..L_b-1) product_(n=0..W)
        (x_b*R_j^t-q^[n-c_b(t)]),                 (6)

up to acquired monomial units. No collision factor is divided out.

A safe common-clock OVERSUPERSET replaces the moving inner intervals by [-L_b+1,W]. Its leaves correspond to canonical n in[-L_b+1,W+L_b-1]. Since L_b<=4k and all these indices are O(k), inequality(2) remains valid with a larger harmless constant below N; transposes are likewise safe. Thus this replacement is lawful for factor-or-recovery semantics, though it can create additional decodable zeros. It is not an exact scalar equality or reverse original-edge predicate.

For a supplied b, the row-root polynomial is an ordinary geometric string of length L_b and the enlarged clock has length O(k+L_b). The old engine acquires and evaluates(6)'s supersuperset in

    soft O(L_b+sqrt(L_b*(k+L_b))).                 (7)

There are O(B) b-values with L_b=O(k/B+1). Summing(7) gives at best the direct bound soft O(k+k*sqrt(B)) for that approach, whereas simply acquiring the whole cell costs soft O(k). It does not even beat the known per-cell route. Base R_j can have small order, including R_1=1; no inverse of 1-R_j^h is assumed. The exact relation R_j^k=q^(1-j) is retained, not replaced by a root-of-unity condition.

Across all cells, even the lists of b-string starts can number soft O(k²). Therefore(5) is not an initialized soft-k whole-family algorithm. The attempted generic string-by-string norm readout has been executed and charged; invoking a short word or a floor description does not pay the missing collective scalar.

## 6. Precise acquisition still needed

The new complete primitive is now simpler than the pair resultant: over all j and dyadic B, evaluate the canonical-phase norm on the NONAXIS congruence differences |a|<A,0<|b|<B, across n=0..6k+1, optionally with cell/n prefixes and transposes. It needs no literal-edge filter, axis factors, pair multiplicities or reconstruction of original rectangle points. Its starts and clock carry are explicitly(5).

An actual advance must amortize these norms across the N-dependent modular slopes a=bN*j^-2 modk AND the b-dependent canonical carries, rather than applying(7) to each string or constructing all their starts. This report supplies no such amortization theorem, and no obstruction to one. Global deduplication of formal rows or numerical residues could help only with a proved algorithm and coverage/recovery ledger; no small deduplicated alphabet is assumed. The original goal remains open.

## Credit and scope

The weighted rectangle coverage, its original public filter and transpose proof are prior credit to the authoritative shiftcoverage packet's dense-box-coverage.md. Stationary canonical phases and the output-sensitive original colour enumeration are prior trace-packet credit. The ratio/canonical difference identity is a derived finite identity independently obtained by the parent and quantum agent; this report records its complete cost and the nonaxis refinement. All acquisition claims above use the existing monic geometric-product engine and the inherited short-annihilator extractor. No new literature theorem, numerical evidence, general no-go result, or sixth-exponent solution is claimed.

### Coordinated per-cell batching refinement

The quantum agent's recursive-products.md improves the INDEPENDENT string-by-string completion in(7). Use a common safe clock envelope and group the at-most-two possible progression lengths L_b. Build G_L(Z)=product_(t=0..L-1)(1-R_j^t Z) once. Blocking a clock interval of length K=O(k) into blocks of d gives a degree-Ld polynomial and O(BK/d) evaluation starts, with cost soft O(Ld+BK/d+B+L). Choosing d near sqrt(BK/L), with endpoint rounding, gives soft O(B+L+sqrt(LBK))=soft O(k) per cell. Everything is polynomial multiplication/evaluation; no 1-R_j^h inverse or small-order premise is needed. This matches the already paid whole-cell method, improves only the independent sum in(7), and does not amortize all colours to soft k. The full collective acquisition and its improved rate remain open.
