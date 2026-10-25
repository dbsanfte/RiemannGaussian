# Independent audit of the selected-prefix and digit-mask primitive

24 October 2026. **PASS. No corrections requested.** Exact frozen source reviewed: `/tmp/semiprime-implicit-thin-encoding-20261024/digit-mask-attempt.md`, SHA256 `300952af3de79e56b9c90d4fe02c756e640273a3e2db444010c0c79d7cb07400`. No source, draft or repository file was edited. This review certifies the specified ONE-mask primitives, not a full matrix encoding or factoring query.

## Actual mask contract and cutoff

I checked the cached primary Schonhage construction, Section 2.2, in the already pinned thin-products PDF. Its p-hat rows give precisely the singleton p entries, negative column pairs -(e0+e2), -(e1+e3), and zero inner restrictions; q-hat gives the stated negative row pairs -(e0+e1), -(e2+e3). These are the INNER coefficient masks. The complete tensor linear forms also contain outer variables; the source does not claim to acquire those outer row-band sums. A zero digit makes the specified inner-mask form zero, not a theorem that every outer contribution of the full tensor term vanishes.

For m radix-four digits, each nonzero inner digit has one or two possible entries, hence the actual support has at most 2^m=sqrt(D) indices before clipping. The cost claim correctly requires D=Theta(b+1), or retains t explicitly if D is larger. It also explicitly handles the degree-b boundary coefficient instead of dropping index D from an undersized coefficient vector.

The most-significant-digit enumeration is valid under the cutoff. Prefixes determine disjoint numerical radix intervals; only one interval per depth straddles b, and prefixes whose least feasible completion exceeds b are pruned. Every surviving prefix has a valid leaf below it, so there are O(m(t+1)) visited branches including boundary/rejected children. Metadata and weights are actually computed. Native polynomial bounds on b,D make these logarithmic-digit costs legitimate; larger metadata is separately charged. No digit factorization of the Gaussian-binomial coefficient tensor is assumed.

## Section 2: all arbitrary selected factorial prefixes are initialized

For b<=2 the direct branch is complete. Otherwise d is the least power of two at least sqrt(b+1), so d=O(sqrt b) and d<=b. The dyadic polynomials B_(2^s) are actually acquired by doubling and coefficient scaling, with a geometrically summed O(d) coefficient budget. All necessary q powers are paid.

There are exactly floor(b/d) FULL blocks, evaluated only at g=0,...,G-1. Their products and prefix products acquire f(dg), including g=G. The last partial block is not expanded beyond b. A requested n=dg+r uses its actual g and binary partition of r. Each contributing B_(2^s)(q^(dg+o)) covers only factors whose indices are <=n<=b. These unaligned starts are explicitly acquired; they are not assumed to be a fixed list of already known powers.

At a fixed length there are at most T requested starts. One monic MPE costs soft(2^s+T); summing sizes gives soft(d+T), including the logarithmic number of request incidences. Combining each residual with its acquired full-block prefix finishes all requested f(n) in soft(sqrt(b+1)+T). Repeated requests and evaluation points are harmless. Divisors in MPE are monic, and the algorithm never divides by a prefix value. Thus the lemma is valid over the actual composite ring/constant-rank algebra, even as a value computation when a factor vanishes.

For the coefficient application, the separate guard really supplies units 1-q^r through b. In the native block application b<=L<C, so this is within the paid short-difference range; the construction introduces no overhang beyond b. The standalone contract is stated more generally with the same guard through its actual b. No characteristic-zero or hidden-field order premise is substituted for it.

## Sections 3--4: selected coefficients and the non-parity mask

The coefficient identity is the correct q-binomial identity. All denominator factors f(a),f(b-a) are actual acquired units, and their inverses over the quadratic algebra use its explicit norm/conjugation and scalar extended gcd. The prefix request set has at most 2t+1 entries. Binary powers, digit weights, all requested coefficients, x powers and the final sum therefore cost soft(sqrt b+t+m), including nonunit x and the a=0 convention. No final answer, c_a or target-dependent mask value is inverted.

With the stated D sizing, t=O(sqrt b), so ONE full selected inner mask is acquired in soft sqrt b. This is a real sub-b coefficient/value acquisition, not a compressed name for a degree-b vector.

The first actual left non-parity pattern has exactly supported indices 0 and 8 and weight -1 on both. The displayed c_8 has sign plus, q exponent 28 and the correct eight numerator/denominator factors. For b<8 only the constant contribution survives; for b=8 the formula gives q^28. No guard beyond the stated b is needed. The two-free-digit support {0,2,8,10} and positive weights also check, with the interval cutoff understood. These are symbolic specializations, not evidence for a general digit-tensor rank claim.

## Section 5: ONE fixed mask at all consecutive giant arguments

Write gamma for the supplied clock base called Q in Section 5, to distinguish it from the fixed mask label. The identity

    sum_(g>=0) L_Q(x0*gamma^g) T^g
      =sum_(a in S_Q) (w(a)c_a x0^a)/(1-gamma^a T)

is exact over a commutative coefficient ring. Each coefficient and geometric base is acquired. The fraction product tree uses only polynomial products/sums, with soft t total coefficient work. The final denominator has constant term one, so truncation, formal inversion through length R and numerator multiplication cost soft(t+R), without spectral-node separation or a Vandermonde inverse.

This computes ALL R actual consecutive outputs, including their startup, cancellations, aliasing and zero coefficients. No starting amplitude or independent initial terms are assumed. x0 may be zero/nonunit; its inverse is not needed. The native clock gamma=q^(-b) is an actual power of the certified unit q. The total soft(sqrt b+t+m+R) claim is therefore correct. It is explicitly not an arbitrary distant-index output theorem, nor one fixed-order recurrence for every higher mask; the denominator may have degree t.

## Whole-query boundary and bit costs

All counts include actual support enumeration, O(T log b) tail starts, fixed-rank inverses, exponent/index bits and all returned R residue values. The primitive needs its actual fixed q and guard. A different q or mask must pay its own data unless another sharing algorithm is proved. Taking unions can request b coefficients; outer row-band sums, output boxes and the terminal product remain separate operations.

The source clearly leaves ALL leaf encodings, all-Q acquisition, outer sums, box sums and original zero-safe factoring reduction unacquired. A zero of this masked linear form is not assigned the original norm-leaf decoder. Its positive claim is exactly one sparse inner tensor mask, or that same mask on a fully charged consecutive clock, over the stated ring and dimension contract. No matrix speedup, endpoint contraction, full-query exponent gain or generic lower bound is inferred. Exact reviewed bytes pass.
