# Independent review: completed quadratic-lift collapse

26 October 2026. Paper-only independent review of `quadratic-lifts.md` §§1 and 4. No repository changes, tests or numerical campaign. The finite contraction is valid with the two explicit normalization repairs communicated to the author: use shifted weighted roots in all zero-based clock products, and recompute carries relative to canonical square-stratum phase representatives before their endpoint gate. The review below specifies those repairs; final author-text verification follows separately.

## Arithmetic, completion and coverage

For nonaxis a=gA,b=gB, n=K/g, the stationary congruence becomes A j²=BN modulo n, where A,B,N are units. The at-most-two square-root branches modulo n and the odd-lift rule with epsilon=1 (n even), epsilon=2 (n odd) are correct. Each branch has g/epsilon lifts. With v=j0^-1 modulo H, d=(BNv²−A)/n is an actual integer. Expanding the inverse phase gives the stated quadratic formula (1). Cubic truncation requires epsilon³ K/g² integral; the supplied parity factor indeed provides the otherwise missing 2-power for even g. This is not an unlicensed claim that g² divides K.

For each distinct acquired pair, completing to all valid unit colours preserves its weighted coefficient bound and stationary phase. Hence every added hit in the correct factor bin has the same exact-integer provenance; original witnesses remain. This changes the old multiset and is an overcover, not scalar equality. Deduplicating coefficient pairs is safe for coverage. Every completed row and its multiplicity must be counted in the NEW residue target.

For fixed g the signed hyperbola bound is O((K/g²)log K) coefficient pairs. Multiplication by at most 2g colours and summation of 1/g over divisors of 2*3^e yields soft K total rows. All row metadata have O(log N) bits. The explicit total-row-count check <16H ensures any good hit count is <R; retain the stated finite-controller branch if it fails. Each branch retains its tag modulo K/g and therefore the common n*=3^ceil(e/2) tag. Added rows in incorrect bins may be rejected or yield verified factors; no provenance is inferred for those bins.

## Essential normalization repairs and endpoint proof

The physical weighted interval is i in [-M0,M0]. Define Z0=q^M0*y0 and T_j=q^M0*y_j. All products indexed t=0,...,h−1 must use Z0 and T_j. A boundary t corresponds to physical i=t−M0, and the scalar beta label is

    E=ell+a+bN−H(t−M0).

The centered Q (or Q/2) must next be converted to the canonical phase e in [0,m). Relative to that FINAL representative define the integer carry directly by

    ell(j)−ell(j0)=(H/m)*e+H*k_j.

Because the phase difference lies in (-H,H) and 0<=e<m, k_j is in {-1,0}. A conservative {-1,0,1} bound is also valid. Thus the same four original boundary indices t=-1,0,h−1,h suffice. One must not first discard centered carries and then silently reduce the phase again modulo m.

Screen these actual boundary gaps by norms and coordinates. Proper gcds factor; continuing saturated point equality licenses beta^(2E)=1. Here b!=0, |a|<=K and bN dominates the centered phase and the O(Hh) endpoint term since N>256H² and h=O(K^(3/2)). Thus E is a nonzero O(log N)-bit integer in every bin. The existing short-label extractor is legal and is charged once only on a terminating branch; its N^(31/192) cost fits soft K and is not called polylogarithmic. Original axes are handled separately, not by this dominance argument.

If all endpoints are units, carried and canonical uncarried rows have exactly the same hit counts and tags over the finite interval. Their scalar products may differ by boundary units. This is predicate/residue equivalence, not numerical scalar equality or cancellation through a nonunit.

## Square strata and exact finite product

For odd g use m=g and phase Q; for even g use m=g/2 and phase Q/2. In either case m=3^a, the quadratic coefficient is a 3-unit, and completing the square is legal public modular arithmetic. For a>0, valuation-2r nonzero squares have one residue class modulo 3^(2r+1), size L=3^(a−2r−1), and multiplicity 2*3^r. The zero square has multiplicity 3^floor(a/2). The case a=0 is the singleton with multiplicity one. The affine unit transformation of a square stratum is exactly one canonical AP modulo m, not an assertion about an uncarried ordinary integer quadratic image.

Writing D=3^(2r+1), L=m/D and qhat=pi^(H/m), one has (qhat^D)^L=q. Therefore u=v−Li is a bijection from 0<=v<L, 0<=i<h to [-L(h−1),L−1]. With shifted Z0 the displayed product identity (4) is exact, including its start and length Lh. Attach the known square multiplicity. The singleton uses L=1 and base q. There is no root-of-unity specialization or discarded phase digit.

For nonzero strata L<=g/3<=sqrt(K/sqrt(3))/3, while h<=8K^(3/2)+9. Consequently Lh<16H on the native K>16 range with ample slack. Singleton h<16H is already the original guard. Each base is pi to a 2,3-smooth exponent, so actual prepared roughness preserves its local order from q, at every field component. Each string therefore has at most one hit.

## Full initialized cost and residue readout

For fixed (g,r), the common base and length permit shared evaluation at all acquired starts. There are O((K/g²)log K) starts. Its cost is soft(J_gr+sqrt(J_gr Lh)); all tails and monic evaluations are paid and collision values need not be inverted. The strata sum is bounded by soft(K+sqrt(Kh)), with geometric factors 1/(sqrt(g)*3^r) and 1/g for zero strata. With h=O(K^(3/2)) this is soft K^(5/4), not a lower bound and not a sixth-rate gain.

A fully explicit no-jet completion uses ALL string values, which the shared engine supplies. Norm/coordinate classification either factors or certifies each value globally zero/global unit using the nonsplit field. The acquired 0/1 string flags are exact hit counts because each string has at most one hit per component. Multiply by its known square multiplicity and branch tag, then sum. This supplies the actual completed-family additive residue pair; a scalar product alone should not be called that pair without this flag/readout step.

The remaining g=1 bank retains the old K-by-h scale for this implementation. This does not exclude another algorithm. The positive new finite statement is completion followed by O(log g) AP-string contraction per coefficient branch, with carries, boundary units, multiplicities and tags all accounted for.

## Final corrected-draft disposition

I read the author's stable corrected §4 after notification. **PASS; both normalization repairs and the explicit all-string-value residue fallback are now integrated.** Formula (4) and all acquired starts use Z0=q^M0*y0; endpoint labels use physical index t−M0; final canonical carries are recomputed directly from the original phases and lie in {-1,0}. The one-hit flag readout includes the square multiplicities and branch tags and does not infer a weighted residue pair from one aggregate zero bit. The opening and conclusion correctly state that §4's lawful completion supersedes the old mask-preservation requirement for coverage while retaining the old rate. No further substantive correction is required.

The primary agent additionally made the axis scope explicit: g=1 controls the nonaxis content sum, while the separately retained axis bank may also retain the old query scale. No claim that all remaining inputs reduce solely to primitive nonaxis rows is made.
