# Independent review: Christoffel/Beatty products

26 October 2026. Read-only symbolic review, no experiments or repository edits. **PASS for the updated draft**, including the improved inherited-backend bound soft(tau+sqrt(k)), where tau is the minimum of the four inverse/reflected slopes. The all-colour materialized-start conclusion is unchanged.

The floor-r quotient intervals begin at A_r=ceil(rk/theta) and end just before ceil((r+1)k/theta); their lengths are h or h+1 and partition a=0,...,k-1 exactly. The acquired starts x_r=z*W^A_r*C^r give Eq. (2) with no omitted endpoint. Inverse-slope reindexing is a permutation of the modular graph, proving Eq. (3).

For Eq. (4), a=0 is exceptional. For a>0, the new residue under k-theta is k-(a*theta modk). Therefore

    P_(k-theta)(z)=(1-z)*prod_(a>0)(1-z*U^a*V^(k-r_a)),
    P_theta(z*V^k;U,V^-1)
       =(1-z*V^k)*prod_(a>0)(1-z*U^a*V^(k-r_a)).

Cross multiplication gives precisely the printed reflection and its sign. No boundary division is licensed if 1-z or 1-z*V^k is nonunit.

## Sharpened paid scalar algorithm

Partition the theta acquired starts by length h and h+1. Each part is an instance of the inherited JOINT geometric-product evaluator: theta_l unit row parameters and one common clock W, of length l. Its cost is soft(theta_l+sqrt(theta_l*l)). A product tree can build the chosen baby polynomial directly from factors 1-W^i*X, followed by monic multipoint evaluation at the starts and the ordinary tails. This uses only supplied unit inverses, never an order or a reciprocal 1-W^n. Repeated starts and W=1 or C=1 remain legal.

Summing the two groups gives soft(theta+sqrt(theta*(h+1)))=soft(theta+sqrt(k)), since theta*h<=k and theta<=k. The theta starts, their powers, and the partition are charged explicitly. For theta=1 this recovers the expected soft sqrt(k) scalar factorial bound instead of materializing its degree-k kernel. This improvement is an application of the existing joint evaluator to the new exact quotient decomposition, not a new universal norm algorithm.

The updated draft now uses the sharper bound and labels direct degree-h materialization only as the weaker alternative. No order information is silently assumed.

## All-colour aggregate and native guards

There are phi(k)=k/3 unit colours for k=2*3^e. The square map has kernel {+1,-1}, so theta=j²/N has exactly phi(k)/2=k/6 distinct values. For any x, at most 4x slopes can have min(theta,k-theta,theta^-1,k-theta^-1)<=x, because each of the four maps is injective. A linear-size distinct-slope set consequently has a quadratic sum of those minima. Hence materializing theta starts at one of these transformed slopes still costs Omega(k²) across the full family, even after granting the cheapest transform. This is scoped to that explicit materialized constructor, not all recursive evaluators or a smaller coverage family. The counting observation alone would not license division by reflection boundaries; the updated operational reflection below avoids that division entirely.

For j!=1, its canonical inverse J in [1,H) is not1. Thus k*N*(1-J) is a NONZERO O(log N)-bit exponent for V^k. A proper gcd factors; a saturated equality invokes the inherited T_ext=soft N^(31/192), not a polylogarithmic extractor. With O(k) colours and at most one terminating extractor, whole-family factor-or-unit preparation remains soft k. A certificate V^k-1 unit does not give an order of W or C; none is needed.

The unwrapped character product does not include canonical q-carries automatically, and the modular box does not meet the low-product cutoff automatically. The draft explicitly retains both missing interfaces. The a=0 factor 1-z is harmless only at an actual supplied nonzero guarded clock phase; z=1 is a tautological zero and cannot be silently included in a physical predicate.

## Full-box coverage statement

At the true colour, the k modular graph points are stationary. Nonnegative coefficients and 0<=lambda<H give the printed index span. Either two integer indices coincide, or the closest gap is less than (P+Q)/H+1/(k-1), as stated. Because theta permutes residues, distinct points have B!=0, and |A|,|B|<k imply BQ-A!=0 for Q>k. The exponent edge gap is therefore a genuine nonzero short annihilator, even when the DIFFERENCE row is outside the old hyperbolic cutoff. This uses the general consumer, not an invented old physical leaf.

The O(k) short-gap bound requires the explicitly stated constant-balance hypothesis P+Q=O(sqrt N). It is not an all-semiprime conclusion. Materializing k points for each colour costs k²; compressing the Christoffel word alone does not acquire their polynomial product or canonical-carry version. The draft makes no false completed-coverage or target-cost claim.

The primary word and short-rational-generating-function results are used only for their word/SUM interfaces; no field-only rational denominator or scalar PRODUCT theorem is imported. No faster complete native query follows from this review.


## Updated operational reflection: verified zero-safe

Read the updated draft. Put tau=k-theta, z'=z*V^k, U'=U,V'=V^-1. For every a>=1, its transformed residue is k-(a*theta modk), so

    1-z'*U^a*(V^-1)^(a*tau modk)
       =1-z*U^a*V^(a*theta modk).

Compute this transformed product OMITTING a=0, and multiply the original factor 1-z. This is an exact polynomial equality at zeros, with no boundary inverse. The first quotient block alone is shortened by one and its start updated; an empty block is skipped. It may introduce a third length h-1, but still only constantly many length groups, with total J_g*h_g=k-1. The same Cauchy-Schwarz cost is soft(tau+sqrt(k)). Applying inverse reindexing first gives the other two slope options and preserves this exact ledger. Thus the minimum-of-four bound is operational, not merely a formal cleared ratio. All all-colour lower-accounting and physical-mask qualifications above remain valid.
