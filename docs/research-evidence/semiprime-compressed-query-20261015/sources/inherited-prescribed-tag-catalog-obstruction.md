# Any prescribed input-independent sparse per-tag index catalog misses the retained majority

2026-10-15. New classical extension of the actual-source endpoint argument. The endpoint proof v2 is unchanged. This is not a lower bound for input-dependent sampling or arbitrary scalar algorithms.

## Theorem and exact quantifiers

Fix the historical scale M, original ordered prime-pair supply and candidate-prime menu as in endpoint-band-counterfamily.md. Before varying N=P Q in that supply, prescribe for every candidate auxiliary prime m and every tag 1<=j<m a finite SET of signed integer indices I_(m,j). These sets may depend arbitrarily on m,j (and the fixed scale), but NOT on N once m,j are fixed. Let

    |I_(m,j)| <= B_*,   B_* = O(M^.970),
    K_* = O(M^.020)

bound their size and the consecutive candidate-prime menu, with fixed implicit constants. Then the number of original inputs for which ANY observed original first-seed residual

    gamma^(N+delta_j)-gamma^(m² i),  i in I_(m,j),

is nonunit in EITHER hidden field at ANY allowed candidate m is

    O(K_* B_* M^5) <= O(M^5.990).

The empty-catalog case B_*=0 is vacuous. Deleting these inputs together with the frozen soft O(M^5.994) deletion leaves Omega(M^6/log² M) actual inputs on which ALL prescribed observations are units in BOTH hidden fields, even though the complete canonical seed rectangle has native forced coverage.

The retained counterfamily may DEPEND ON the prescribed catalog family. The theorem does NOT assert a single counterfamily simultaneously defeats all possible catalogs. In particular the following inference is invalid: choose an N-dependent index after the theorem and claim the same deletion estimate. Libraries selected using the actual a_j,b_j,delta_j,N or previous observed residuals are outside the stated input-independent contract, except when the entire possible library at fixed m,j was already prescribed within this bound.

The counting claim has no restriction on index magnitudes: an arbitrary fixed i only translates an interval. For an actual soft O(m) probe implementation, B_* must be polylogarithmic and the index exponents must have polynomial-logarithmic bit length, with paid enumeration and powering. The polynomial width M^.970 and polynomial prime menu are coverage-only allowances.

## Historical hypotheses used

Use the verified archived full-euclid-all-hit-obstruction.md §2 (E5)–(E10), and the frozen first-K candidate extension (J4) in the journal. Exact source pins are inherited from endpoint-band-source-pins.json. We use:

* P,Q in a fixed balanced bin inside [cX,X], X=M³, and actual pair mass Omega(M^6/log² M).
* For every retained candidate m, m~M and projected gamma has exact local prime orders R_P,R_Q>16m²; P,P-1,Q,Q-1 are units modulo m². These are proof-side supply facts, not supplied order or factor oracles.
* A necessary selector envelope gives, at fixed P,m, O(G_m+1) half-open Q boxes of width <=m², with sum_m(G_m+1)=O(K_*M).
* Literal seed data: a_j in {1,...,m-1}, a_j j²=N mod m, I_j=j^(-1) mod m, D_j=(N-a_j j²)/m, b_j=centered(m,-I_jD_j), delta_j=a_j+m b_j-2a_jj, and -3m²<=delta_j<=m².

No new prime-distribution estimate, local-orbit separation premise or source normalization is introduced.

## Local count in one Q box

Fix an admissible P,m, its actual local prime order R=R_P, and one half-open Q box of width <=m². We count hits in the P-field.

For any fixed tag j and any fixed prescribed index i in I_(m,j), local vanishing is equivalent to

    Q+delta_j-m²i = k R.                         (1)

The equality uses P=1 mod R to reduce N=P Q. Across the WHOLE Q box and all allowed source states at this tag, Q+delta_j-m²i lies in an interval of length <=5m²<R. Therefore there is at most ONE possible integer k. Crucially i is fixed while Q varies; it may differ between tags, and its absolute magnitude does not affect this count.

Put

    A_j = j²-2Pj+P mod m.

Reducing (1) modulo m and using P Q=a_j j² gives

    a_j A_j = P k R mod m.                      (2)

Separate tags as follows.

### Nonexceptional false tags

If A_j is nonzero and j!=P mod m, equation (2) fixes at most one canonical slope a_j. That fixes Q mod m. If two such partners Q,Q' qualify at the same (j,i), their actual lift difference gives

    m(b_j(Q)-b_j(Q')) = -I_j P (Q-Q') mod m².

Subtracting (1) therefore yields

    (1-P I_j)(Q-Q') = 0 mod m².

The coefficient is a unit since j!=P mod m. Hence Q=Q' mod m², so the half-open box contains at most one integer Q. Summing at most B_* prescribed indices over fewer than m tags gives O(m B_*) states.

### Exceptional tags

The monic quadratic A_j has at most TWO roots in F_m. At such a tag (2) may allow all slopes, so retain all m-1 possibilities a. Each exceptional tag is false: at j=P mod m one has A_j=P(1-P), which is NONZERO because both P and P-1 are units modulo m. For every fixed slope the same full-lift argument as above gives at most one Q in the box. Thus the two exceptional tags contribute at most 2 B_*(m-1)=O(m B_*) states.

### The own tag

At the unique tag j=P mod m, A_j=P(1-P) is nonzero. Therefore (2) still gives at most one slope and hence one Q class modulo m, for each prescribed i. The coefficient 1-P I_j now vanishes modulo m, so do NOT apply false-tag uniqueness. Instead a half-open box of width <=m² contains at most m+1 integers in that one class modulo m (in fact m suffice with strict half-open conventions). This contributes O(m B_*) states.

No own-index range exclusion is required. Prescribed indices may lie anywhere, including the canonical interior; what matters is their independence of Q at fixed m,j.

Combining the three cases gives O(m B_*) bad integer Q states per box. Counting prime Q only decreases the bound.

## Whole-supply count and simultaneous consequences

There are O(X)=O(M³) possible integer P values in the original factor bin. Once an admissible actual P is fixed, its actual R_P is fixed; the local count is uniform in R_P, so no additional cofactor enumeration or sum over v_P is needed. Summing boxes and candidate primes gives

    O(B_* X sum_m m(G_m+1)) = O(K_* B_* M^5).

Swapping P and Q costs only a factor two and proves the claim for both hidden fields. The count is on the ORIGINAL supply, so it can be united directly with all prior deletions without intersecting a thinner independently constructed family. At B_*=O(M^.970) and K_*=O(M^.020), exponent 5.990 is strictly below the frozen 5.994 loss and both are below the original supply exponent 6.

On each remaining input every residual from the prescribed catalog is a unit. Therefore every multiplicative expression built from these residuals and their inverses is also a unit, and its gcd with N is one. This defeats collision support acquired solely from those probes, including arbitrarily weighted ratios. Additions that create new residuals, input-dependent index choices, adaptive libraries outside a prescribed bounded union, and a genuinely implicit acquisition of the full long query remain outside this result.

## Relationship to the endpoint theorem

The fixed-constant O(M^.970) size hypothesis includes the 4w+2 endpoint indices when w<=M^.970. The endpoint theorem handles a public prescribed length and all tags near its two endpoints. It is a special case of this catalog theorem (with B_*=O(w+1)); its own-tag deterministic exclusion gives a slightly stronger local statement, but is unnecessary for the majority count here. The new theorem permits each tag to have a completely different sparse prescribed index set, with arbitrary signed locations. It still does not provide the missing nearlinear long-query algorithm.
