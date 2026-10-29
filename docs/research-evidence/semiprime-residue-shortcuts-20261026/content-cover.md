# Imposed 3-content: explicit coverage/clock trade-offs

26 October 2026. Paper derivation; no repository edits or experiments. Inputs and decoders are those of clock-phase/parity-cover-audit.md and unique-weighted/unique-cover.md. K=2·3^e, H=K², N≤K^6, prepared factors >16H, and the good π-clock order is >256H². The public parity selector is retained throughout.

**Result.** There are explicit covered scalable families, but neither of the two natural imposed-content constructions gives a power saving. A genuinely coarse *phase-support* cylinder costs more than a coarse stationary colour domain. Their distinction is the decisive accounting point. The following is not an algorithm lower bound.

## 1. The least-cost imposed-content lattice

Let g=3^t, 0≤t≤e. Demand a=gA,c=gC and parity a+cN=0 modulo4. At colour r the remaining stationary condition is

    A r(r+K)=C N mod 2K/g.                         (1)

Here the parity condition at4 and stationarity at3^(e-t) form a core lattice of covolume 2K/g. Multiplying its vectors by g gives a coefficient lattice of covolume 2Kg. Weighted Gauss reduction therefore gives a covered vector with

    a² B⁴+c² N² ≤ (4/sqrt(3)) K g B² N.            (2)

One such vector for every original unit colour gives a public covering family of at most K/3 rows, acquired in soft K. Zero core contents beyond t are allowed in this coverage construction; they should be classified by their ACTUAL content rather than being called exact-g rows.

Take

    D_g=ceil(sqrt(2KgN)),
    M_g=ceil(4D_g/H)+2, h_g=2M_g+1.

The exact same weighted Cauchy–Schwarz argument as the parity audit covers every true index. After the known public parity phase, the common padded clock has length M_g+1=O(g^(1/2)K^(3/2)). Thus the direct per-colour construction only stretches the old horizon by sqrt(g); its query upper bound is soft(K+K^(5/4)g^(1/4)). The constant parity gain remains, but no exponent gain follows.

For the native short-unit screen and exact-integer provenance, use only g for which the displayed actual h_g plus padding remains <16H and the leaf-label magnitude stays below256H². For example g≤K/1024 suffices for all sufficiently large K under N≤K^6: h_g<8sqrt(2g)K^(3/2)+9 gives h_g+2<16H, and the full integer exponent bound is 8D_g+(7/2)H+H<256H². If K<1024, that sufficient range has no positive g. No amended family is asserted in that case: execute the already prepared parity-family fallback (g=1 with its separately proved bounds). More generally use that fallback whenever this new sufficient range is empty; this is an actual public branch, not a claim that the new range covers small K. This is a sufficient public range, not a claim about maximal admissible g. Actual mixed-leaf localization is unchanged; its coefficients have O(log N) bits and remain far below N in this range.

## 2. Actual phase classes, not stationary domains

Suppose a row has EXACT 3-content g, so a/g and c/g are 3-units. Dividing its phase polynomial by g and completing the square modulo 3^(2e-t) shows that its support among colours modulo3^e has at most

    2·3^floor(t/2) ≤ 2sqrt(g)                     (3)

members. To verify the bound: the congruence is a unit-leading quadratic modulo3^M, M=2e-t. A square congruence has at most 2·3^floor(M/2) roots; reduction to residues modulo3^e divides this count by 3^(M-e), because M≥e and the following native periodicity holds. Write F=f/g over the 3-adic integers (g divides the canonical ell), with unit leading coefficient. At the defining colour j, v3(F'(j))≥e-t and F(j)=0 modulo3^M. Therefore its discriminant is divisible by3^(2e-2t). At ANY root x modulo3^M, F'(x)^2 equals that discriminant modulo3^M, forcing v3(F'(x))≥e-t. Consequently F(x+3^e z)-F(x) is divisible by3^M for every z: the linear term has valuation at least2e-t=M and the quadratic term at least2e≥M. Each root residue modulo3^e thus has exactly3^(M-e) root lifts modulo3^M. This yields the displayed bound. Odd-unit CRT adds no multiplicity. The exceptional zero discriminant is included.

By contrast its STATIONARY eligible domain may contain 2g colours. Replacing phase-class size by that domain size would produce a false factor-sqrt(g) saving.

If one insists on covering all colours by exact-g rows and uses the uniform horizon in §1, even the optimal hypothetical phase packing needs at least phi(K)/(2sqrt(g)) rows. Its row-clock mass is therefore at least a constant times K^(5/2), for N=Theta(K^6), at this assigned common horizon. This is a scoped price for this uniform-horizon construction, not a lower bound for variable exact windows or scalar algorithms. Reaching the maximal fibre bound at every colour has not been proved and is unnecessary for this conclusion.

Mixed-content families do not automatically evade this ledger: each content contributes its actual phase fibres and its own horizon. A new saving would require a coverage theorem concentrating colours on unusually large fibres with *shorter actual windows*, or a shared contraction of many phase classes. The existing min-cost laminar selection remains available when its determinant/disjointness hypotheses hold; they must not be imported unchanged into the enlarged (2) ellipse.

## 3. A genuinely coarse-colour cylinder cover

There is a second, fully explicit construction whose supports contain whole coarse cylinders. Let m=3^v with 0≤v<e and let a cylinder be r≡j modulo K/m. For its phase polynomial f(X)=aX²+ell X+cN to vanish modulo H on EVERY point j+(K/m)z, the exact odd-prime finite-difference conditions are

    m² | a,  Km | f'(j).                          (4)

The value f(j)=0 modulo H is supplied by the canonical lift. Since f'(j)≡a j-cN/j modulo H, (4) is equivalent to

    a=m² A, c=m² C,
    A j²=C N mod K/m,
    A+CN=0 mod4.                                 (5)

The second condition in (4) forces the claimed divisibility of c; no modular division by m is used. Conversely substitution gives f(j+(K/m)z)=0 modulo H directly. The parity lift is legitimate because the core parity condition is retained.

For each of the phi(K/m)=K/(3m) cylinders choose a shortest vector of the core lattice in (5), whose covolume is 2K/m. Scale by m². Its full coefficient lattice has covolume 2K m³. Thus

    a² B⁴+c² N² ≤ (4/sqrt(3)) K m³ B² N,
    J≤K/(3m), h=O(m^(3/2)K^(3/2)).                (6)

Every true factor colour is in a chosen cylinder, and the inherited index formula supplies a covered hit. Extra supports are harmless for the factor-or-localized-query contract; this note does not assign them an unjustified cylinder tag or assert global uniqueness. The exact mixed-label decoder handles any emitted nonunit AFTER localization. No singleton or residue-ratio promise is used: acquire row products by the shared engine, select a row whose product norm is nonunit, and recursively bisect its actual clock interval until an individual nonunit leaf is obtained. In a commutative ring a product of units is a unit, so a nonunit parent always has a nonunit child. Norm gcds may return a proper factor immediately; a saturated norm is not itself decoded as a relation, but is refined to an actual leaf (and subjected to the inherited coordinate/norm guard there). The cost of the geometric-product subqueries along a selected path sums to the original bound up to logarithms. The resulting actual label has second mixed exponent a+cN≠0: nonaxis coefficient bounds give |a|≤2Kg/sqrt(3) in §1 or2K m³/sqrt(3) here, both<N, whereas axes are nonzero multiples of their least allowed coefficient. Thus the licensed leaf decoder, including its once-only soft-K saturated branch, applies even with multiple hits in either component. Complete row support metadata or uniqueness would require a separate proof if a one-moment consumer were desired.

Acquisition uses K/(3m) weighted Gauss reductions, roots and parity starts, hence soft K. Take D=ceil(sqrt(2K m³N)) and the corresponding M above. The sufficient range m³≤K/1024 automatically excludes v=e; when empty, use the original parity-family fallback rather than asserting cylinder coverage at a nonexistent new scale. For the admitted scales it gives the same explicit short-clock/order margins as §1. Integer labels remain O(log N) bits. Unit padding is the actual endpoint gate of the parity audit; no quotient by an unclassified endpoint is allowed.

The resulting joint-query upper bound is

    soft(K+sqrt(Jh)) = soft(K+K^(5/4)m^(1/4)).       (7)

It gets worse as the cylinder grows. Here the row reduction is real and covered; the cost loss is also explicit. A stationary domain with m colours cannot simply be substituted for this actual phase cylinder: guaranteeing the latter forces the extra m² scalar content and hence the m^(3/2) clock stretch.

## 4. Remaining constructive lever

These executions isolate a narrower target than arbitrary row thinning: find a covered family of large ACTUAL phase classes whose physical windows grow by less than their support size, or evaluate several of their finite-clock functionals jointly without separately materializing those windows. Merely imposing content, coarsening the stationary modulus, or multiplying a row does not supply that theorem. The public parity selector is a genuine constant-factor improvement and composes with both families, but does not change these powers.

Prior credit: original weighted Gauss coverage and variable-window engine; unique-weighted phase-support partition; clock-phase public parity lattice, endpoint gate, and full-fibre scaling criterion. No new sixth-rate supplier or factorization bound is claimed here.

## 5. Conditional hybrid frontier: a separated-cost evaluator would change the outcome

For sufficiently large K, choose the largest m=3^v with m³≤K/1024. Then (K/27648)^(1/3)<m≤(K/1024)^(1/3), so m=Theta(K^(1/3)), with v<e. The acquired cylinder family has

    J=O(K^(2/3)), h=O(K²),

and the explicit native guards of §3. The inherited joint-product cost becomes O-tilde(K^(4/3)), worse than the old bank. Nevertheless this family has a different useful aspect ratio: an initialized evaluator costing

    O-tilde(J^(3/2)+sqrt(h))

would process it in O-tilde(K). The same hypothetical evaluator is too expensive on J=Theta(K), h=Theta(K^(3/2)). This is a conditional hybrid opportunity, not an evaluator established here.

In general, write m=K^x with 0≤x≤1/3, ignoring fixed constants and ceilings. A multiplicative cost J^alpha h^beta gives exponent

    alpha+(3/2)beta+x((3/2)beta-alpha),

and an additive cost J^alpha+h^beta gives exponent

    max(alpha(1-x), beta(3/2+(3/2)x)).

These describe upper-bound substitutions for the acquired family, not lower bounds, and setup still costs O-tilde(K). The endpoint x=1/3 is attainable with the conservative constant in the guard, rather than requiring the boundary h=16H.

The required evaluator interface is stronger than a weak unique-hit first-jet ratio: this cylinder cover may have multiple hits, and no global singleton or common-mark promise was proved. A sufficient interface is the actual product (or a truthful zero/nonunit predicate) on the full acquired family, together with the ability to repeat it on arbitrary row subsets and consecutive clock subintervals at the same stated cost. Such hereditary calls localize one nonunit leaf by balanced bisection; their total cost is O-tilde(K) at this aspect ratio, including logarithmic depth. Proper gcds terminate early; saturated norms must continue to an actual individual mixed relation. The existing once-only factor decoder then costs O-tilde(K). No empty block is interpreted through an unguarded jet ratio.

Equivalently, an evaluator may return a nonunit ACTUAL leaf with its acquired (row,index) label directly. Merely returning zero for an unlocalized aggregate, a formal kernel vector that can vanish at the good component, or a projective ratio licensed only by unique-hit hypotheses is not the interface asserted sufficient here. All coefficient acquisition, starts, endpoint gates, component-unit guards, repeated localization calls, and final extraction must be included in the hypothetical bound. No such separated-cost evaluator is claimed.

### 5.1 Structural credit: the cylinder construction retunes the conductor

The preceding aspect-ratio family has a simpler exact interpretation, observed by the parent audit. Set K'=K/m and H'=H/m². In (5), a=m²A,c=m²C and canonical ell is divisible by m². Put ell'=ell/m²; it is the canonical centered phase modulo H', since division carries [-H/2,H/2) exactly to [-H'/2,H'/2). Then

    y_j=(pi^ell' barpi^(A+CN))^(m²),
    q=(pi^H')^(m²).

The core lattice and ellipse are precisely the ordinary parity-cover construction at conductor K', with the old stronger prepared group elements retained. The support colours are residues modulo K'. The inherited local orders are coprime to3, so m²-powering is injective in each relevant subgroup: original and rooted leaves have exactly the same zero/nonunit status, although their products and first derivatives are not numerically equal. The rooted clock is acquired by exponentiating pi to H'; no unknown-order root extraction is used. Its short node differences are certified by the original q-screen, because equality under the rooted clock would imply equality after m²-powering. All actual label decoding retains the original soft-K budget and preparation.

Also H'≡4 modulo8, and A+CN≡0 modulo4, so the public parity selector applies literally to the rooted bank. Its window has h=O(sqrt(N)/(K')^(3/2)); ceiling conventions in §3 only introduce a bounded endpoint overcover, which must retain its explicit endpoint gate if padded. Thus J=O(K') and the frontier above are a quantitative retuning of the existing parity family, not an independent new coverage miracle. The useful conditional question remains whether an initialized evaluator with the separated dependence can exploit that retuned aspect ratio under the already paid stronger preparation.

### 5.2 Retuned unique cover and a row-index consumer

The retuned COMPLETE parity ellipse also supports the already proved unique-support partition. Its determinant bound is4K'/sqrt(3)<3K'; pure-conductor content still satisfies g²<K'; maximal-3-content direction selection and singleton fallback are unchanged. These are metadata statements independent of N≤(K')^6. Do NOT apply that smaller-scale size hypothesis: the horizon, alias bound and short-node guards instead use the ORIGINAL K preparation and the explicit safe range m³≤K/1024 above. Acquisition of the complete retuned incidence bank and its unique partition is O-tilde(K') within the original O-tilde(K) budget. Thus there is exactly one good-field leaf in the whole selected bank, J≤phi(K').

This licenses a weaker alternative to the hereditary product interface in §5. Assign each selected row a DISTINCT public integer mark j in1,...,J. Suppose an initialized evaluator returns a weak normalized first-jet pair (V,U) with V nonzero at the good field and U/V=j* there, where j* is its unique hit row. No old residue tag modulo the smaller conductor and no HH call are needed.

Norm-classify V: a proper gcd factors; gcd one licenses a global inverse; gcd N declines this wrong-bin candidate and NEVER licenses inversion. In the correct bin the nonzero good-field value excludes that last branch. For c=U/V, its tau coordinate has gcd divisible by the good prime. A proper gcd factors; gcd one rejects a wrong attempt; gcd N licenses treating c as scalar. Scan gcd(c-j,N) for j=1,...,J (or use an acquired product tree and localization). At the true j* that gcd is proper or N. In the latter case retain that actual row. The scan costs O-tilde(J), since all labels have O(log N) bits; J<16H<good prime prevents distinct integer row marks from colliding there. Wrong bins supply only bounded candidates and cannot suppress later correct attempts.

Finally evaluate and localize JUST the retained row over its actual shortened clock, with the inherited division-free geometric-product engine. Its h=O(K²) gives O-tilde(sqrt(h))≤O-tilde(K) work; a nonunit path exists at the good component. Norm saturation is refined to an actual leaf, whose nontrivial mixed label uses the once-only original O-tilde(K) decoder. Thus a whole-bin weak unique-hit row-index pair is sufficient after rebuilding the retuned unique partition; arbitrary hereditary oracle access is not necessary for THIS stronger-input variant. An analogous normalized pole-root output may identify the row by gated norm tests against its acquired numeric roots.

This is a concrete cheaper consumer for a retuned scalar target. It still does not acquire the first-jet pair, the selected residue, or the pole-root output. The conditional separated-cost evaluator of §5 would suffice if it outputs this correctly marked weak pair with its initialization and all component guards included. The general nonunique cylinder-product interface in §5 remains valid as a separate option.
