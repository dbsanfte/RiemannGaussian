# Independent review: uniform weighted-rectangle short-shift cover

26 October2026. Read `dense-box-coverage.md`, including its direct canonical-phase proof. The uniform coverage theorem, counts, constants, bit sizes and nonzero-gap recovery PASS. It is an enlarged-family coverage result with soft-k descriptors and quadratic-scale explicit point incidences; it does not acquire a faster collective query. No tests or repository edits.

## Rectangle count and exact acquisition

For each b, stationarity fixes one a residue modulo k. Thus n>=B floor(A/k)>=2k−B>=k. Also A<2k²/B+1 gives n<=B ceil(A/k)<2k+B/k+B<=3k+1, so integer n<=3k. These statements hold for every colour and public dyadic scale, without distribution assumptions.

Explicit enumeration costs O(k) points per rectangle: for each0<=b<B compute a0=[bN j^-2]_k, then output a=a0+t k<A. Its work is O(B+n), not a scan of the area AB=Theta(k²). There are phi(k)=Theta(k) colours and Theta(logk) scales, hence Theta(k²logk) point incidences for this materialized construction, with polylogarithmic bit work per point. Descriptions, dimensions, colour inverses and slopes alone cost soft k. The report correctly distinguishes these interfaces and does not claim a quadratic lower bound for compressed or deduplicated evaluation.

## Canonical phase and uniform true scale

The phase proof is valid for ALL lattice vectors, independently of |ab|<k. With P=j+kt,

    P^-1=jinv−kt*jinv² modH,

and the change in aj+bN jinv is kt(a−bN jinv²), divisible by H on Lambda_j. Since NP^-1=Q modH, the canonical phase is−aP−bQ modH. Therefore every true-colour rectangle point has the claimed integer stationary I and beta^E=q^I modP. This does not import the old bounded-hyperbola admission rule.

From P>16k² and sqrtN<=k³, rho=kP/sqrtN>16; P<=sqrtN gives rho<=k. A public dyadic B has rho/2<B<=rho. Since A−1<2k²/B, b<B and lambda<H,

    I<2P/B+BQ/H+1<5sqrtN/k+1<=5k²+1.

All quantities used to describe rows have O(logN) bits, including the temporarily unwrapped phase bN jinv. No floating-point index or unknown-factor computation is used by the algorithm; sorting the true I values is an existence argument only.

For n>=k distinct indices, their smallest adjacent gap is less than(5k²+1)/(k−1)<6k on k>16. If indices repeat, distinct points give gap0. Thus the stated s in[0,6k] is uniformly guaranteed, including unbalanced inputs. The loose constant6 is safe.

## Nonliteral labels, origin and decoder

Subtracting the two actual stationary equations gives

    E_v−E_u−Hs=(P−1)(Delta b*Q−Delta a).

Here |Delta a|<A<=2H<Q. If Delta b!=0 the second factor cannot vanish; if it is0 then distinct points have Delta a!=0. Hence the guaranteed edge has a nonzero short label. A proper gcd factors, and a globally saturated equality invokes the old extractor on beta and this O(logN)-bit label. No wide exponent or old |ab|<k premise is needed.

The guaranteed labels E_u,E_v cannot coincide: equality implies q^s=1 moduloP; for0<s<=6k<16H this is impossible, while for s=0 it contradicts the displayed nonzero gap. This argument works for all point pairs, not only the Delta b=0 case mentioned in the prose.

Origin(0,0), E=I=0, may remain as a reference point, provided edges use DISTINCT points and the integer-gap check. A shift0 product must exclude diagonal self-comparisons. Alternatively origin can be omitted: n>=k−1 and(5k²+1)/(k−2)<6k still holds for k>16, so the same constant survives. The report's chosen inclusion is sound and does not justify ordinary whole-row deletion in this new auxiliary construction.

For wrong colours/scales, literal edges can indeed occur. Therefore the bare unfiltered all-pairs product is not the claimed factor predicate. The stated factor-or-certify-all-edges-literal interface, including shift0 separation, is correct. A known additive zero or literal equality is not assigned the extractor.

## Optional descriptor-only literal-cell filter

A useful additional audit consequence is available without point expansion. Let g=gcd(j−1,k). A rectangle has NO literal integer edge at any s in[0,6k] between distinct points if A<=H/g. Indeed changing b makes |E_v−E_u|>=N−3H>6kH. At fixed b, Delta a is a multiple k, and equality moduloH requires its magnitude to be at least H/g. This contradicts |Delta a|<A.

Conversely, if A>H/g, the rectangle contains origin and(a=H/g,b=0). The latter lies in Lambda_j and has canonical E=H, so this cell has a literal shift1 edge. Thus this particular bad-cell condition is exact and descriptor-computable.

The true cell is never rejected. Since g divides P−1 and H, the q-order is at most(P−1)/g. Its bound>16H gives g<(P−1)/(16H)<=rho/16. With B>rho/2>8g,

    A=ceil(2H/B)<H/(4g)+1<=H/g,

where H/g>=k>16 supplies the final margin. Filtering out A>H/g therefore preserves this uniform coverage and removes all literal within-cell comparisons in the stated range. This optional refinement still leaves the quadratic implicit point population and its uncomputed aggregate. It does not produce a new scalar query, and cross-cell comparisons must not be added without their own gap checks.

## Boundary and final scope

The canonical node is exactly U_j^a V_j^b q^(-t_(a,b)); its carry cannot be dropped in a Christoffel product. The auxiliary coefficients can exceed the old mask, and their stationary indices reach O(k²), but the pair gap is O(k) and has the independently proved nonzero decoder. The promised collective query remains unacquired. The report accurately claims new uniform short-shift COVERAGE, not an all-semiprime soft-k algorithm or a new factoring exponent.

## Bare filtered product and the global-zero strengthening

After retaining only A<=H/g, the bare product over distinct points WITHIN each retained rectangle and shifts0<=s<=6k has no literal integer gaps. Thus every nonunit leaf, including accidental ones, has the proper-gcd or nonzero-short-annihilator consumer. The original true rectangle guarantees this product is NONUNIT at P. Without another coverage argument it is not yet guaranteed zero at Q; a value/gcd or exact-nonunit oracle suffices, whereas a zero-only endpoint requires both prime components.

A constant-description extension supplies that stronger endpoint. Attach the TRANSPOSE of every retained point set, with (a,b,lambda)->(b,a,lambda) and colour j'=N j^-1 modk. The same-phase statement follows from the exact unit lift j'=N jinv modH; this does not require either side to obey the old low-product mask. For the actual P rectangle, the transposed pair has stationary indices I'=(bQ+aP+lambda)/H=I at Q, and therefore forces the SAME s at Q.

Every transposed pair is nonliteral automatically. For a fixed original a there is at most one b in[0,B), since theta is a unit and B<=k. Distinct points therefore have distinct original a, and their transposed labels E'=b+aN+lambda satisfy

    |E'_v−E'_u|>=N−k−H>6kH.

Hence no shift0..6k is literal within a transpose either. Take the product of WITHIN-rectangle edge factors and WITHIN-transpose edge factors, with distinct endpoints; do not add cross-cell or original-to-transpose comparisons without checks. This bare filtered aggregate is globally zero, since the original pair supplies P and its transpose supplies Q, and all of its leaves are legally recoverable. Point count and descriptor cost increase only by a constant. Its collective scalar readout remains unacquired and no rate improvement follows.
