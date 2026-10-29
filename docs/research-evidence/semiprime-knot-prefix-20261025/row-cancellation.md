# Native-row finite cancellation audit — 2026-10-25

Result: an exact native opposite-row identity gives support-preserving multiplicity removal for the zero-only prefix. It reduces each ordinary opposite pair to one contiguous two-sided q-interval with two known-unit holes. This is a real row-family contraction, but only a constant-factor reduction: length remains Theta(m), and no soft(k) prefix algorithm follows. No unproved discrete-log relation, modular root-of-unity interpretation of beta, or canceled collision denominator is used.

## Prior work read and credited

Read the actual scalar catalogue and swap erratum, /tmp/semiprime-native-family-sharing-20261024/deletion-and-grouping.md, /tmp/semiprime-character-acquisition-20261022/discriminant_sieve/actual-anchor-overlap.md, and the q-hook normalization conclusions in the tensor/character/Toda reports. These already establish root-coset tiling, the axis-only public deletions, the gap between formal q-hook units and specialized collision values, and the danger of canceled common roots. They are not counted as new progress here.

The exact deletion simplification is useful: nonaxis rows are not publicly deleted; only two horizontal axis rows and their two swapped partners disappear. Complete root cosets therefore survive throughout the nonzero-product catalogue. The opposite/sign involution preserves these axis exceptions, complete-swap pruning, and diagonal status. A central or pair-difference gcd screen may terminate with a factor/extractor, but must not silently delete a hit and continue.

## Actual native opposite involution

For a retained row (a,b,lambda), E=a+bN+lambda and x=beta^E. If 0<lambda<H, its opposite (-a,-b,H-lambda) has

    E'=H-E,       y=q/x.

If lambda=0, its opposite has E'=-E and y=x^-1. This distinction is essential for the uncentered catalogue. No sign closure x->-x is assumed. The row involution is known on integer labels and costs soft(J) to acquire, with no group-order computation.

On the continuing centrally screened branch both x-1 and y-1 are units. For lambda!=0 this also certifies x-q is a unit, because y-1=(q-x)/x.

Write delta_x(t)=(x-t)(x-t^-1)/(x-1)², so Delta(t) is the product of all row delta factors. A native pair y=q/x satisfies the exact identity

    delta_y(t)=(x-qt)(x-q/t)/(x-q)².                    (1)

Thus the pair's m-prefix is

    P_pair(m)=prod_(i=1)^m
       (x-q^i)(x-q^-i)(x-q^(i+1))(x-q^(1-i))
          /[(x-1)²(x-q)²]^m.                           (2)

All displayed denominator factors are already certified units. This is a direct identity over Z/NZ; it does not require units among the collision factors in the numerator.

## Exact deduplication for the zero-only predicate

For m>=1 the exponent multiset in (2) is

    [1,m] + [-m,-1] + [2,m+1] + [1-m,0].

Interior exponents 2..m and 1-m..-1 occur twice. The four endpoints 1,m+1,-m,0 occur once (the displayed interval convention handles m=1 by empty interiors). Exponents 0 and 1 contribute units by central processing. Consequently define the division-free product

    B_pair(m)=prod_(r=-m)^(m+1), r!=0,1 (x-q^r).          (3)

For squarefree N=PQ, P_pair(m)=0 modulo N iff B_pair(m)=0 modulo N. This is because a prime divides a product iff it divides one factor, independently of multiplicity, and denominators and deleted r=0,1 factors are units. Equation (3) has 2m factors versus the original pair's 4m factors. For lambda=0, delta_(x^-1)=delta_x and the pair prefix is a square, so the same squarefree zero test may simply retain one row.

The same multiplicity-removal implication applies globally: replace every opposite pair by (3), retain one representative for lambda=0 pairs, and keep multiplicities only when needed for an exact scalar value. The total new product is zero modulo N iff the original full prefix is zero modulo N. This is safe deduplication, not rational cancellation. At a hit there is no 0/0 evaluation and no factor containing the only prime witness is erased entirely.

Saturation handling remains the established prefix consumer: the transformed predicate agrees exactly with the original zero predicate, so the first-zero index gives a nonunit original Delta(q^i), and the final scan uses original x_j-q^±i labels. No transformed leaf or new annihilator license is needed.

For a repeated-prime modulus, replacing a square by one copy need not preserve zero modulo p²; (3)'s zero equivalence explicitly uses the actual distinct-prime semiprime setup.

## Paid algorithm and its remaining cost

1. Acquire opposite pairs from the known labels, respecting public deletion and complete swaps, in soft(J) metadata work.
2. For a requested m, construct each row-group product (3) as the product of two ordinary finite q-Pochhammer intervals, with the r=0,1 factors omitted by interval endpoints, not by inversion of unknown leaves.
3. Evaluate the aggregate product with the existing geometric multipoint/product method, then test exact zero. The degree/interval parameters change by constant factors, so this remains soft(J+sqrt(Jm)). Evaluating each pair separately instead costs up to soft(J sqrt(m)).

One can also start from the full interval [-m,m+1] and divide by (x-1)(x-q), because these two factors are specifically certified units; this is an optional legal implementation. None of the doubled interior factors may be divided out on an unscreened branch.

The union interval grows by two endpoints per increment of m; its known starting product at m=0 is 1. This cheap initialization does not pay for all later endpoints across J pairs. Repeated doubling still requires the full interval products. No new additive soft(J+sqrt(m)) acquisition was found.

## Complete modular root cosets: actual tiling, no torsion collapse

Within a complete root branch lambda=lambda0+d*s, 0<=s<L, with dL=H, set rho=beta^d. Then rho^L=q, not 1. Its row points are x_s=c rho^s. Multiplying across rows and q-clock indices produces an interleaved exponent rectangle. Since q=rho^L, its q-index spacing L fills a contiguous rho interval when all s are present. This is the previously credited exact root-coset tiling.

It is not the root-of-unity identity prod_s(1-X rho^s)=1-X^L: the latter would require rho^L=1, whereas rho^L=q has large local order. The tiled product has LM factors at the finer base rho. A finite fermionic, Gaussian-binomial or quantum-dilogarithm rewrite must still acquire that long finer-base product, or prove a new contraction across different (a,b) cosets. Complete roots modulo H are not a multiplicative torsion coset in R.

Opposite pairing above commutes with coset tiling at the support level, but merely replaces repeated interval points by one copy and extends the exposed endpoints. It supplies no inverse divisor with which a whole coset product cancels safely.

## Coboundary and lattice-boundary tests

A proposed exact rational coboundary Delta(t)=R(qt)/R(t) for a nonzero rational R would have valuation zero at t=0 and t=infinity, because t->qt preserves both valuations. In contrast Delta(t)=G(t+t^-1)/G(2) has valuation -J at both places, with unit extreme coefficients. Thus this literal rational coboundary is impossible for J>0 over the generic coefficient field. Multiplying by a Laurent monomial cannot repair both valuations simultaneously. This is only a test of the literal scalar rational-coboundary ansatz, not an algorithmic lower bound.

More general finite lattice-boundary quotients may have numerator/denominator factors with common zero sets. Prior overlap work already notes that canceling them can remove an interior hit. In the present row family the sign relation produces repeated *positive* factors, not opposite divisor multiplicities. Equations (1)–(3) show exactly the remaining positive interval, so counting a canceled q-dilogarithm ratio as a short endpoint answer would discard its surviving factors.

The pair's uncentered reflection is r->1-r rather than r->-r. There is no supplied parameter shift (a,b,lambda)->(a',b',lambda') taking every row point x to qx while preserving the same finite catalogue with short boundary. A change lambda->lambda+H changes the integer representative outside [0,H); restoring it returns the same row and moves the q-clock by one, so it is not an additional acquired native row. Root lifts and carries must remain explicit.

## Cauchy / pentagon interface

Finite Cauchy determinant identities can turn a rectangular product into a determinant divided by two within-family Vandermondes. The acquired native x_j differences are not all certified units: different native labels can give equal points, or a difference divisible by an unknown prime. Taking those inverse Vandermondes would need individual factor screens or a division-free resultant implementation. The prior q-hook/Sylvester work supplies formal normalization and some early-pivot cleanup, not all these specialized inverses or a scalar contraction at soft(k).

KMT finite mutation identities (https://arxiv.org/html/1611.05969, Proposition 4.3 and equation (5.9)) preserve a formal partition function by introducing a finite summation over flow/dimension indices. The actual opposite-row relation above supplies commutative row factors and a reflection; it does not acquire noncommuting Weyl generators or a sum with the Gaussian weights needed to collapse that rectangle. Introducing such a state sum without a paid contraction would move the LM/Jm support into the state indices. No concrete pentagon cancellation across distinct native (a,b) cosets was established.

## Outcome and specific next lemma

The constructive output is the zero-safe native opposite-pair replacement (3), including its uncentered carry, all units and all interval boundaries. Its paid completion has the old soft(J+sqrt(Jm)) cost. A genuine next advance would be a theorem contracting the collection of intervals (3) across distinct acquired native pairs in soft(J+sqrt(m)), or a coverage-safe subcollection with that paid aggregate cost. The complete root cosets and swap witness guarantee do not themselves provide that theorem. No new soft-k prefix primitive or factoring bound is claimed.

## Positive refinement: the correct half-center trace fold

The root supplied the useful refinement of (3). Pair the negative and positive endpoints r=-s and r=s+1, for s=1..m, and set

    W=x+q/x,
    C_m^half(W)=prod_(s=1)^m(W-q^-s-q^(s+1)).

Then the exact finite identity is

    B_pair(m)=x^m C_m^half(W),                            (4)

because (x-q^-s)(x-q^(s+1))=x[W-q^-s-q^(s+1)]. Opposite rows x and q/x have exactly the same W. Thus one can actually acquire a monic modulus G_half(W)=prod_pairs(W-W_pair) of degree J_nonzero/2 in soft(J) work, from the surviving lambda!=0 rows. This is a genuine factor-two degree reduction at the half-center; it does not assert a false factor-two reduction for center-zero traces of the uncentered catalogue.

Normalization is paid:

    W-(1+q)=(x-1)(x-q)/x.

Central processing of both opposite rows certifies these factors as units. Therefore every 1+q-W_pair and G_half(1+q) is a unit, and the reciprocal normalization centered at 1+q is legal. The actual target zeros are preserved by (4), whose extra x^m is a unit.

There is also a known square root of q, with no root extraction: eta=beta^(H/2), since k=2*3^e makes H even. Writing v=x/eta gives

    W/eta=v+v^-1,
    (q/x)/eta=v^-1.

In integer exponents this is exactly E->E-H/2, after which E'=H-E becomes negation. This recentering is legal and acquired. It changes the clock roots to eta*q^s+(eta*q^s)^-1 in normalized trace coordinates; it does not turn them into the old integer-centered clock without accounting for the half shift.

### Opposite closure after actual deletion and pruning

Re-read the pinned deletion-and-grouping proof with its actual hard-branch assumptions N>256k^4 and k>16. It proves no b!=0 row is publicly deleted. The two deleted b=0 rows are

    (k,0,H-k),   (-k,0,k).

These are each other's opposites under lambda->H-lambda. Their complete-swap partners

    (0,k,H-k),   (0,-k,k)

are also each other's opposites. Hence the four exceptional removals preserve opposite closure exactly, including axes. Complete-swap pruning commutes with the opposite involution, and deleting the complete diagonal subset also preserves it. This justifies forming all lambda!=0 pairs on the actual remaining list, rather than an idealized complete catalogue.

### The lambda=0 class is tiny and can be paid away

Here k>16 implies e>=2. For lambda=0, the root equation requires 3^(2e)|ab, since gcd(N,3)=1. A nonzero product has |ab|<k=2*3^e<3^(2e), impossible. Thus lambda=0 occurs only on the four axis rows, giving at most four points or two inverse pairs, before further pruning.

Their full length-M contribution can be computed and gcd-screened with the existing fixed-degree geometric product evaluator in soft(sqrt(M)) work. If it is nonunit, the existing prefix localization and original signed-leaf/extractor consumer finishes within that bound, up to logarithms. If it is a unit, all its shorter prefix contributions are units, and the class can be removed from every later zero query. Thus the complete lambda=0 branch can be discharged in soft(k), without assuming it absent.

This screening matters for zero-only interfaces. In general one cannot OR two zero-only answers for two disjoint row classes: each class can be nonzero while their product is zero modulo PQ. Paying the constant-size lambda=0 nonunit screen avoids that error and leaves a single half-center zero-prefix target.

### Full-family folded query and cost

After the lambda=0 screen returns unit, the complete original prefix is zero iff

    prod_pairs C_m^half(W_pair)=0 modulo N,

equivalently the resultant of acquired monic G_half and C_m^half is zero. The known x^m factors and all central denominators are units and need not be evaluated for this predicate. Original labels are retained for the final signed scan. The folded modulus has degree J_nonzero/2, with all its coefficients acquired in soft(J); its full query is still paid by the old geometric evaluation machinery in soft(J+sqrt(Jm)). Only constant factors improve.

### Changed normalized hypergeometric family

The natural normalized coefficients are

    H_m^half(W)=(-1)^m q^(m(m+1)/2) C_m^half(W)
                         /[(q;q)_m(q²;q)_m]
               =(xq,q²/x;q)_m/[(q;q)_m(q²;q)_m].         (5)

All denominator exponents are <=m+1 and are below the promised local orders throughout the target range. At W=1+q, H_m^half=1, which also verifies the normalization constant explicitly. The coefficient generating function is

    Psi_half(z)=2phi1(xq,q²/x;q²;q,z).

Its q-Euler transform again has an exactly rational prefactor:

    Psi_half(z)=(1-z)^-1 2phi1(q/x,x;q²;q,qz).             (6)

This is a valid finite-precision formal identity after scalar denominator checks. The transformed series retains both generic upper parameters; no infinite product is charged as an available scalar. Direct finite subtraction gives

    H_m^half-H_(m-1)^half
      =q^m(1+q-W)(xq,q²/x;q)_(m-1)
                         /[(q;q)_m(q²;q)_m],

so the rational prefactor sums a new explicitly factorial-weighted family. This does not itself acquire the large coefficient H_M^half.

After one coefficient decimation the actual even coefficients are

    H_(2n)^half=(xq,xq²,q²/x,q³/x;q²)_n
                      /(q,q²,q²,q³;q²)_n.               (7)

They form a 4phi3 at base q² after omitting one built-in q² factorial. The half-center symmetry does not cancel any of these factors for generic x. Thus the concrete tested q-Euler/parity route does not supply a closed two-parameter doubling algorithm for the folded whole-family query. This is the remaining tested step, not a general obstruction to another quadratic transformation.

The payable positive output is therefore the native half-center fold (4), degree J_nonzero/2 acquisition, legal boundary G_half(1+q), and the constant-size lambda=0 screen. No exponent improvement is claimed.
