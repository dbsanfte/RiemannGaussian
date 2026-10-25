# Independent scalar binary-mask elimination review

2026-10-24. Verdict: **PASS**. No required fixes remain. Reviewed exact `/tmp/semiprime-recurrence-endpoint-20261024/scalar-elimination.md`, SHA256 `cc5ad6f52a941b0f150a8be8acc908ead21ef33c3de5b1312e1b61bb6c17f9ec`.

The prior draft c739697783f6bffa5839713e0d03a0de71d8b2d3f7f06c4092e87bf0916216ec was mathematically sound for r>=1 but left B=1 implicit. The final version explicitly states the positive-depth condition and trivial B=1 mask. No source or repository mutation was performed by this reviewer.

## Exact native image and initialized lifts

The original own relation HI=a_jP+Q+ell_j reduces modulo B=2^r to the displayed public mask because P is odd and Q=N/P modulo B. H=m² is odd, so its inverse modulo B is acquired. These are public binary-modulus inverses, not inverses of nonunit residue-ring collision factors. The mask is an exact image of all odd factor residues; it is a covered overestimate of possible true witnesses, not a proof that every masked index hits.

The one-bit expansion is correct, including its full next-level offset alpha. A parent image alone cannot determine alpha because different preimages can carry differently. The final algorithm retains actual factor balls and recomputes their rational values, so it does not assume that missing state.

## Regular balls: exact class image

Let delta=2^t z and k=v2(a v0²-N). Direct subtraction yields
  f(v0+delta)-f(v0)=delta*(a-N/v0²)+N delta²/(v0²(v0+delta)).
For k<t, divide by 2^(t+k) and set c=(a v0²-N)/2^k. The source's normalized rational function
  F(z)=z*(c+a v0 2^(t-k)z)/(v0(v0+2^t z))
is exact; in particular its denominator does not omit a factor of v0. Denominators remain odd for all integer z. Modulo two this is z, and its derivative is odd. For a lift z+2^s, the quadratic Taylor remainder has valuation at least 2s; for s>=1 this vanishes modulo 2^(s+1). Consequently exactly one lift realizes each prescribed next output bit. The induction gives a permutation modulo every required power of two.

The actual domain parameter spans 2^(r-t) residues, while the normalized output needs only 2^(r-t-k) when this exponent is positive. This proves SURJECTIVITY onto the whole output class, not just containment. If t+k>=r the image is one residue. Thus the emitted class modulus 2^min(r,t+k) and its acquired offset are correct. All calculations are modular rational arithmetic with certified odd denominators.

## Critical balls and O(log B) acquisition

For k>=t, both terms in the difference have valuation at least 2t. A critical ball is therefore constant modulo B once 2t>=r. Otherwise splitting the actual factor ball into its two children and reevaluating is legitimate.

The active critical condition is a v0²=N modulo 2^t. For even a it is impossible. For odd a it is a square-root condition for an odd unit and has at most four roots modulo 2^t for t>=3. The source's proof via (x-y)(x+y), exactly one of the two factors having valuation one, is correct. Hence each depth has boundedly many critical balls and boundedly many regular children. Depth is at most ceil(r/2), so total nodes and emitted classes are O(r). No odd-residue list of size B is constructed.

Applying the invertible affine output map preserves each dyadic modulus. Such residue classes are laminar: two are disjoint or one contains the other. Their explicit residues/moduli therefore suffice to remove duplicates/containments at soft-r cost and leave an exact disjoint image representation. Across J rows, the acquired state and small-integer work are soft J, including bit costs, with O(J log B) metadata.

## Cardinality and bounded-modulus statement

For even a, the difference factor a-N/(vw) is odd, so f is injective on odd residues and maps them onto the single odd output class. Its exact cardinality is B/2, preserved by the affine output map.

For odd a, if v2(a-N)<=3 choose v0=1; otherwise v0=3 gives v2(9a-N)=3. In either case 1<=k<=3. A ball of radius 2^(k+1) is regular and maps onto a class of modulus 2^(2k+1)<=128. For small B the corresponding truncated class is a singleton modulo B, so nonemptiness still yields |S_j(B)|>=B/128. The chosen v0 is 1 or 3. Its actual tree path reaches a regular node by depth k+1<=4 unless the constant-modulo-B stopping rule applies earlier. Thus the constructor itself emits this bounded-modulus class; deduplication can replace it only by a larger containing class of no larger modulus. No distribution hypothesis for native a_j parity is used.

This is a lower bound on mask CARDINALITY only. The source does not turn it into an arithmetic lower bound, an actual-source failure family or a distinct-target count. Its constant-density conclusion correctly limits this particular image-pruning mechanism.

## Actual scalar product completion

For class i=c modD with 0<=c<D<=B<=L, all surviving indices in [0,L) are c+Dk with k starting at zero. The known unit transformation z=q^-c Y_j, q_D=q^D preserves the ORIGINAL collision. For fixed D, the two possible horizon lengths are floor(L/D) and ceil(L/D). Grouping by D and length is therefore fully initialized despite different offsets c.

Let K_(D,h) be group sizes. Total acquired labeled classes Ktot is O(J log B). Each group's degree-K polynomial is built explicitly; its block degree Kb and actual h/b giant starts give the source's soft(K+sqrt(Kh)) bound. Summing the square-root terms is justified by Cauchy–Schwarz:
  sum_(D,h) sqrt(K_(D,h)*L/D)
    <= sqrt(L*Ktot*sum_(D,h)1/D).
The reciprocal sum is bounded because D runs over powers of two and there are at most two lengths. Thus the full cost is soft(J+sqrt(JL)). No unknown root-separation guarantee is required by monic product/MPE arithmetic.

Each row contributes a bounded-modulus class. Pigeonholing over D<=128 and the two possible lengths yields a group with a constant fraction of the row LABELS and a constant-fraction horizon. This accurately describes the degree charged by this implementation retaining multiplicities. The source explicitly allows coincident shifted roots and potential instance-specific deduplication; it does not claim their distinct count must be large.

## Localization and global decoder

The masked query is an underset of the original row/index rectangle retaining its own witness. Restriction to groups, rows/classes and k intervals recomputes lawful monic products at no greater parameter size. No desired value is inverted. Each localized leaf retains its original j and i=c+Dk in the original horizon.

I independently read the pinned `uniform-setup-and-query-interface.md` and verified its SHA256 `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`. Section 8 supplies the claimed original-beta bounded global collision decoder, using the acquired global-order and factor-sum margins. The new masks do not change beta or the original index, so this import is legitimate. A proper leaf gcd returns a factor; a saturated leaf gives original global equality and therefore P+Q=1+Hi-delta_j under those inherited bounds. Integer square-root recovery is paid. There is no transformed-base order transfer or unproved algebraic decoder.

## Scope

The exact compressed binary image constructor is a positive acquired native arithmetic filter. It is not an exact arbitrary-F endpoint evaluator, and the report says so. Its completed covered query remains soft m^1.5 at J~m,L~m². No hidden JB residue enumeration, free terminal input, altered horizon, denominator hit deletion or new all-input factoring-rate claim was found. The explicit B=1 edge clarification resolves the only requested adjustment.
