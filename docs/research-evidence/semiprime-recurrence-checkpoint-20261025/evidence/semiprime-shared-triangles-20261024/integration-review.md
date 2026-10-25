# Independent integration review: shared triangles

24 October 2026. Reviewed the two exact integration drafts below, gap-complement-sharing.md, native-pairing-review.md and reviews-shared.md. No draft or repository mutation.

| Draft | SHA-256 |
|---|---|
| /tmp/semiprime-shared-triangles-20261024/journal-append.md | 69aae7e89e1261c2ae80116ce055959938e8e6acbb9a7469081d2ace36801806 |
| /tmp/semiprime-shared-triangles-20261024/agents-append.md | 2006c7e9b70481c3fb878e1a2b4ca19a3394791888f6a0778fd460dabe1ff956 |

Verdict: **PASS for mathematical integration and claim scope. No required content fixes.** Preservation evidence from the prior pass is /tmp/semiprime-recurrence-innovation-20261024/continuation-validation.json; root reports its rerun at 11:40:33 UTC with 270 PASS. This read-only review does not itself revalidate all270 entries or repository-prefix preservation. Final preservation verification and exact-source pinning will be performed subsequently by root's current validate-continuation.py script; this review does not claim that new run has already occurred.

## Exact gap reflection and native realization

For coprime a,m>1, F=am-a-m=(a-1)(m-1)-1=2g-1. The positive gap set and its F-reflection partition [0,F]. Expanding the reflected polynomial negates exactly g factors, proving

    S(z)S(-z-F)=(-1)^g B_(2g)(z).

There is no inverse or cancellation at a hit factor. Native arguments sum to a+m(tau+K+K'). Setting K'=1-a-tau-K makes this sum a+m(1-a)=-F. This is the correct gap-reflection lift; it differs by one from the earlier first-triangle lift condition K+K'=-a-tau, and the drafts correctly distinguish them.

Closing I0 under K->1-a-tau-K requires only endpoints. The overlapping integer index intervals [mK,mK+d-1] merge exactly for a>=3 because d=(a-1)(m-1)>=m. Recomputing their union keeps zero support without dividing overlaps. The a=2 one-index holes are safely overcovered; a=1 has no gap support and is separately supplied as an ordinary AP. The drafts retain these essential exceptions.

## Independent coverage and safety

The map c_j=-N/j modulo m permutes nonzero residues. Opposite tags have opposite residues, so representatives choose exactly one from each pair of nonzero signed residue classes. Each completed AP contains every index with abs(t)<=m²+2m. Since abs(c_j)<1.5m², every signed n with abs(n)<=m³ and matching residue has abs((n-c_j)/m)<m²+1.5m. Thus exactly one sign of every positive n<=m³ prime to m is represented, including P<=floor(sqrt N)<=m³. This is independent coverage of the new completed family; the drafts do not infer it from a rectangle quotient or from gap-denominator support.

Reflection closure gives K endpoints O(m), d<m² and consequently physical leaves O(m³), nonzero modulo m. On the stated hard branch N>256m⁴, m>=17, the explicit envelope lies strictly below N. Saturated products can therefore be localized to proper-factor leaves using original physical labels. No gcd=N value is itself declared a factor.

## Physical clipping is exactly the old factorial interval

For A=16m², W=floor(sqrt N), clipping each representative to A<abs(c_j+mt)<=W selects exactly one of n,-n for each positive n in (A,W] prime to m, and no other absolute values. The signed norm is therefore exactly

    (-1)^nu product_(A<n<=W, m does not divide n)n.

The number of negative factors nu is acquired from O(m) interval endpoint/count metadata. This is a direct product identity, not a quotient with an untested denominator. To relate it to the ordinary integer factorial interval, its removed m-multiples are units: they are m times integers <=W/m<=m², below the prepared prime cutoff 16m². Their correction can be acquired at the already paid soft-m scale. Thus clipping faithfully returns the old factorial norm, not a smaller N-dependent selector.

## Whole-family costs and final claim scope

There are O(m) APs of length O(m²), with total length Theta(m³) in the displayed completed implementation. Common factorial blocking costs soft(B+m³/B+m); B near m^(3/2) gives soft m^(3/2). Metadata is paid separately and does not replace this product acquisition. Restricted products and binary localization retain this bound up to logarithms. The exception a=1 costs soft m and changes no exponent.

The earlier triangle engine still emits Theta(m²) AP starts despite shared binary factorials, common-step transposition and rectangle pairing. The drafts accurately distinguish this implementation count from a generic lower bound. The literature discussion correctly treats explicit inputs/precomputation as charged and does not exclude ring-general methods merely because N is composite.

Reciprocal transport is summarized consistently with the corrected reviewed source: PLUS in the t_j carry, exact original leaf after normalization, enlarged lift range, and a conditional small-submenu unit screen. The full original-menu sufficient condition B>=m/4 is retained without transferring it to the enlarged reciprocal image.

Both drafts explicitly state no new whole-query exponent, no improvement to the separate N^(1/5) benchmark, and no all-semiprime N^(1/6) result. They leave full bit/Lean composition open and preserve the outstanding goal. The reported positive identities and completed coverage are therefore integrated at their actual initialized cost.
