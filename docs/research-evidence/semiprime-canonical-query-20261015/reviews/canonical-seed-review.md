# Independent canonical-seed-query reduction review

2026-10-15. PASS as a conditional reduction. Subsequent native-source discovery confirms this coverage and recovery reduction was already compiled in SemiprimeSeedSumAcquisition; see the provenance correction below. No acquisition algorithm or new Lean theorem is established.

## Hypotheses and public query

Let N=p*r for distinct primes p<=r, auxiliary prime m>=2 coprime to N, m²<=p, and N<=m^6. Let gamma=projectedUnit g m from native LongData. The two local gamma orders exceed 4m² and are coprime, so its global order D is their product and D>16m^4. This is a statement about the projected unit, not automatically the original g.

For the public denominator-one first seed, let a_j,b_j be the native seed coefficients, ell_j=m b_j-2a_j j and delta_j=a_j+ell_j. Native seedOffset bounds give -3m²<=delta_j<=m². Query all j=1,...,m-1 and i=0,...,2m²+1:

    A_(j,i)=gamma^(N+delta_j)-gamma^(m² i).

Negative exponents, if encountered in public power formation, only invert known unit gamma. Public coefficient/target acquisition costs soft O(m) ring work times polynomial logarithms, not O(m³) materialization.

The native WideWrapCoverage.seed_index_bounds was inspected directly. Its exact seed equality m² i=a_j p+ell_j+r gives an integer i in this interval at true tag j=p mod m. Consequently N+delta_j-m²i is divisible by p-1, because N=p*r and a_j p≡a_j modulo p-1. Hence p divides the corresponding residual. The full product necessarily has nontrivial gcd with N. No hidden p is supplied to the algorithm; it is an existential coverage witness.

## Every nonunit leaf suffices: no holes needed

A proper leaf gcd immediately factors N. At a leaf with gcd=N, global gamma equality yields D dividing e=N+delta_j-m²i. Set

    S=1-delta_j+m²i,

so e=N+1-S. Euler/Lagrange yields D dividing phi(N)=N+1-(p+r). Subtraction gives D dividing S-(p+r). The bounds imply

    |S|<=2m^4+4m²+1,
    p<=m³, r<=m^4, p+r<=m³+m^4,
    |S-(p+r)|<=3m^4+m³+4m²+1<16m^4<D (m>=2).

Therefore S=p+r, for ANY globally zero leaf, including a tag different from the forced row. This is strictly stronger than removing at most two false global hits.

Recover p,r as the roots of X²-SX+N. Compute Delta=S²-4N by exact integer arithmetic, its integer square root, test exact squareness/parity, and verify any candidate divides N and lies strictly between 1 and N. For a proven global leaf these checks succeed. All integers have polynomial-logarithmic bit length: S=O(m^4), N<=m^6. Standard integer square root and gcd give polynomial-logarithmic work relative to N in the normal sixth-width regime; no factor/order oracle is needed.

The original proposal's <=2 global-hit count is also mathematically sound under its stated delta bounds and common rectangle: pairwise hit exponent differences have magnitude at most 2m^4+5m²<D, forcing a common integer C=delta_j-m²i; modulo m, N(t²-2t)=C has <=2 tags, and one i per tag. But this count is unnecessary once phase-sum recovery is used.

## Oracle-to-factor algorithm and exact interface

Assume an exact scalar oracle for product_(j in T) product_(i=s to s+l-1) A_(j,i), with arbitrary supplied target sublist T and a common interval, costs soft O((|T|+sqrt(l))*polylog N), including origin shift. First evaluate the full rectangle and take gcd. By coverage it is >1. Return a proper gcd immediately; if it equals N, bisect target list T. Evaluate one child, take gcd, and retain a child with gcd>1; if a tested child gcd is 1, the complementary child's gcd is >1 by the known parent product. No residual inversion is needed. A proper child gcd immediately solves factoring. Once one row remains, bisect the contiguous index interval in exactly the same way. The interval's start is absorbed into the known unit origin gamma^(m²s).

After O(log(m-1)+log(2m²+2))=O(log m) calls, a nonunit leaf is found. It yields either a proper gcd or the exact phase-sum recovery above. Every oracle call has |T|<=m-1 and l<=2m²+2, so the claimed per-call bound is soft O(m polylog N) and the logarithmic number of calls is absorbed. No holes, arbitrary ragged intervals, denominator unit certificates or local-order coprimality with m are required for localization/recovery. Native LongData supplies the large global order and the rest of the upstream routing remains a separate requirement.

## Native theorem provenance correction

The initial check inspected WideWrapCoverage.seed_index_bounds, LocalOrderRouting.LongData and PhaseSumRecovery.integral_global_phase_sum. The latter theorem alone has a shorter merged-index range and cannot literally cover this rectangle. However, the coverage agent subsequently identified already compiled SemiprimeSeedSumAcquisition.common_seed_sum_exact and long_public_route_seed_batch_succeeds covering the canonical seed query and global-sum recovery. Thus the initial claim that this was a new classical range extension was wrong: the elementary argument here is a valid independent check, but the reduction itself is already native. No build was run in this review task.

## Outcome

This reduction validly simplifies the remaining acquisition target to one common rectangle, target subsets and shifted contiguous subintervals. Saturation is resolved by exact phase-sum recovery, not assumed absent. The soft O(m) product oracle itself remains unproved; the reduction does not establish guaranteed one-sixth factoring.
