# Independent gap-complement sharing audit

2026-10-24. Verdict: **PASS**. No required fixes identified. Reviewed exact source `/tmp/semiprime-shared-triangles-20261024/gap-complement-sharing.md`, SHA256 `c5d0b856504dfe7e1ef14deacd4ddc4c033eb1bd5708de2f18e217e20a2fc884`.

This review certifies the displayed integer identities, newly proved universal coverage, safe overcovers and initialized soft m^1.5 construction under the inherited prepared native promises (m odd prime, m>=17, gcd(N,m)=1, N<=m^6, P,Q>16m², hence N>256m^4). It does not establish a new factoring exponent. Source and repository were not edited.

## Frobenius complement and native realization

The gap proof is exact. For r in [0,F], choose its unique m-coefficient i in [0,a-1] modulo a and write r=mi-aj. A gap has j>=1; then F-r=m(a-1-i)+a(j-1) is representable. F itself is not representable: its m-coefficient in any nonnegative representation would be at least a-1, while m(a-1)>F. Thus r and F-r cannot both be representable, proving exactly one gap. Multiplying the factors gives S(z)S(-z-F)=(-1)^g B_(2g)(z), including the sign. This is a denominator-free integer polynomial identity.

For opposite native tags, the centered b relation and c relation agree with the earlier independent affine-batching derivation. The reflected block starts satisfy K+K'=1-a-tau. Their arguments therefore sum to a+m(1-a)=-F. Since tau in {-2,-1,0} and 1<=a<m, the reflection center C lies within [-m,m] (indeed the bound is conservative). The old interval and reflected interval overlap, their union is one interval I, and R(I)=I. Reindexing the partner product by R proves the exact displayed paired-gap product, without assuming any original rectangle hit survives a denominator.

## Empty and thin exceptions

For a=1 the gap set is empty. It supplies no hit coverage, so its separate ordinary progression is essential and correctly included. The equation a_j=1 has at most two j-solutions modulo prime m, forming at most one opposite pair.

For a=2, d=m-1. Consecutive intervals start m apart and omit one index each; the source correctly uses a support overcover by filling these holes. Added leaves are lawful under the same physical envelope and nonzero residue. For a>=3, d>=m, so consecutive factorial intervals overlap or touch and their exact union is the stated interval of length m(Khi-Klo)+d. Removing multiplicity means recomputing this support product, not dividing hit-bearing values.

Because I contains [-m-2,m+2], every merged or filled a>=2 interval includes [-m²-2m,m²+2m]. Its upper endpoint is at least m²+2m+d-1, and d>=1. The separate a=1 interval includes the same uniform range by definition.

## Independent universal integer coverage

The residues c_j=-N/j modm permute every nonzero class. Opposite tags carry opposite classes; one representative per pair thus chooses exactly one element of each nonzero sign-pair. For any positive n<=m³ with m not dividing n, exactly one of n,-n has a representative's residue. Call that signed integer n0. Then
  t=(n0-c_j)/m
is integral, and abs(c_j)<3m²/2 gives abs(t)<m²+3m/2. Therefore t belongs to the uniform progression range, including the separately handled a=1 case. This proves coverage for every such n, independently of the old rectangle correction quotient.

In particular P<=sqrt N<=m³ and P is prime to m, so the new completed progression family has a proper local hit. Its dependence on N only permutes/sign-labels the low residue classes; it does not select a smaller set of absolute integers. The source states this universal-cover limitation correctly.

## Explicit leaf safety

The reflection bound gives
  -2m-2 <= Klo <= Khi <= 2m+2.
With 0<d<m², the merged interval indices satisfy
  -2m²-2m <= t < 3m²+2m.
Using abs(c_j)<3m²/2, every merged/fill leaf has
  abs(c_j+mt)<3m³+(7/2)m²<4m³<N
for m>=17. The a=1 appended interval satisfies an even smaller bound. Every physical leaf has the fixed nonzero residue c_j modulo m, hence is not literally zero. As its absolute value is below N, a nonunit leaf cannot be a multiple of all N; its gcd is proper. Saturated products therefore have valid localization. This verifies the source's stated constant-below-six envelope with an explicit stronger constant.

## Actual aggregate acquisition and localization

The O(m) acquired endpoint pairs specify progressions of lengths O(m²), with total length Theta(m³). This total accounts for the at-most-one a=1 exception: all other representative rows already contain the uniform length-Theta(m²) interval. Choosing block size B~m^(3/2) gives total full-block targets O(m³/B). The common polynomial B_B has degree B and is constructed explicitly. Binary tails require total polynomial degree O(B) and O(m log B) actual target arguments; monic MPE has no node-difference or hit-value inverse. Thus soft(B+m³/B+m)=soft m^1.5 includes initialization, targets and known scale powers.

Binary restriction to rows and then progression indices recomputes products of at most this total size. On a chosen search path logarithmically many such calls suffice, so the same soft bound handles proper-factor localization. The report claims an initialized upper bound for this implementation, not an output-size lower bound on other methods.

## Signed physical clipping

After clipping A<abs(c_j+mt)<=W, every retained physical leaf was already in the proved cover, since W<=m³. For each positive n in (A,W] prime to m, exactly one of n,-n belongs to a representative low residue, and occurs once at its unique integer progression index. Conversely every clipped leaf arises in this way. Hence the integer product equals
  (-1)^nu prod_(A<n<=W, m does not divide n)n.
The number of negative leaves, or just its parity, follows from O(m) exact endpoint/count computations. No root-product quotient or nonunit cancellation is needed for this equality.

The right side is exactly the earlier sufficient interval factorial channel. Its excluded m-multiple product and lower endpoint factorial involve only certified units under P,Q>16m²; direct interval arithmetic is also available. Thus the claimed soft sqrt W<=soft m^1.5 acquisition/localization is supported, while full executable/Lean composition remains separate work.

The source faithfully separates exact gap values, support merging, exceptional overcovers, universal coverage, and the physically clipped identity. No hidden prime input, missing a=1/2 branch, unsupported successful-menu claim, or exponent improvement was found.
