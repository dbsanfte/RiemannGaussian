# Actual first-current coverage and recovery: a clean conditional query reduction

2026-10-15. Mathematical reduction using retained native identities. No new near-linear query algorithm and no newly compiled Lean endpoint. Repository source hashes are in native-pins.json.

CORRECTION, 2026-10-15: further historical inspection found that SemiprimeSeedSumAcquisition.lean ALREADY compiles the original m-1 seed coverage, the larger padded interval bounds, and the every-global-seed-hit factor-sum theorem. Earlier working versions of this report incorrectly called the range argument a new classical extension because they checked only the earlier SemiprimePhaseSumRecovery module. No arithmetic coverage or sum-identity advance is claimed. The distinct contribution here is the clean restriction-stable scalar-oracle bisection contract, replacing the existing explicit jet acquisition interface conditionally.

## Precise status

The uncentered first-current source ALREADY has bounded-prefix collision coverage for every factor ratio after the quadratic small-factor prefix. It is not necessary to prove a probabilistic or character-sum hitting theorem for this source. The native seed-index theorem gives the common interval [0,2m^2+2). Moreover the already compiled common_seed_sum_exact theorem proves any globally zero individual residual in the larger padded seed interval reveals the true factor sum on the actual long-order branch. Consequently a restriction-stable exact scalar query oracle suffices for proper recovery using logarithmically many calls and no derivatives.

This does not assert that every centered half/top-bit subquery covers: those restrictions may omit the witness. It also does not pay for the scalar oracle or the complete routing/bit implementation.

## Source and assumptions

Let N=pq, p<q distinct primes; square inputs may be detected separately by integer square root. Let m>=2 be the public prime with N<=m^6. After the native prefix fails, p>m^2 and m is coprime to N. All algorithm inputs below are public; p,q and the true residue are proof witnesses only.

At every 1<=j<m retain the original seedRow=denseRow(N,m,j,1,false):

a_j=N j^(-2) mod m, 0<a_j<m,
ell_j=m b_j-2a_j j,
delta_j=a_j+ell_j,
E_j=N+delta_j,
Y_j=gamma^E_j, alpha=gamma^(m^2).

Here b_j and c_j are the literal full-N lift coefficients, not an advised field lift. Native seedOffset_bounds gives -3m^2<=delta_j<=m^2. The m-1 seeds, their public inverses/lifts and target powers cost soft O(m) ring/bit work at polylogarithmic operand size: acquire gamma^N once, then gamma^delta_j using known-unit inverses for negative digits. A monic product tree acquires H in soft O(m) as well; the long query remains the unpaid operation.

Assume gamma is the actual projected long-route unit. The native long_global_order_bound gives D=ord_N(gamma)>16m^4. This theorem uses the routed coprime rough local orders; the reduction below needs only the resulting global-order bound, not prime local orders or their values.

## Exact bounded-prefix coverage

Set j=p mod m. Native row_index_exists supplies an integer I with

m^2 I=a_j p+q+ell_j,
quadratic(a_j,b_j,c_j,(p-j)/m)=pI.

Native seed_index_bounds proves

0<=I<=2m^2+1

from m^2<=p<=q and N<=m^6. Its proof uses p<=m^3 and q<=m^4; no bounded factor ratio is assumed. Native quotient_row_power_hit gives

E_j-m^2 I=(p-1)(q-a_j),
Y_j=alpha^I mod p.

Thus the exact common query

A(T,s,l)=prod_(j in T) prod_(s<=i<s+l)(alpha^i-Y_j)

has gcd(N,A({1,...,m-1},0,2m^2+2))>1. This follows for any unit gamma; the long-order condition is needed below for cheap unambiguous global recovery, not for coverage.

The first current really is the t=1 positive seed: publicPairs begins with (quotientSlope mod m,1), and coprimality makes that slope nonzero. Keeping its original source avoids all moving normalization origins. An origin/target phase change is harmless only when the index interval is transported with it.

## Every global leaf gives the true factor sum

Suppose ANY tag 1<=j<m and ANY 0<=i<=2m^2+1 satisfies Y_j=alpha^i modulo N, even if j is not a true factor residue. Define the public integer

S=1-delta_j+m^2 i.

The verified equality implies D divides N+1-S. Euler's theorem implies D divides (p-1)(q-1)=N+1-(p+q). Therefore D divides S-(p+q).

The source bounds give

1-m^2<=S<=2m^4+4m^2+1,
p+q<=m^3+m^4<=2m^4.

Hence |S-(p+q)|<=4m^4+4m^2+1<16m^4<D for m>=2. The divisible integer is zero, so S=p+q. The discriminant S^2-4N=(q-p)^2 then gives both factors by exact integer square root, with proper-divisor checks.

This is ALREADY compiled as SemiprimeSeedSumAcquisition.common_seed_sum_exact for every r<seedLength(m), where its seedLength_bounds theorem proves 2m^2+2<=seedLength(m)<=4m^2 for m>=4. Thus our interval is a direct subinterval of the compiled theorem, not a new classical range extension. The elementary bound above restates its mechanism for the smaller exact interval. Unlike general positive-denominator columns, t=1 has no fractional-phase exception. There are no false global leaves requiring deletion or separate row-quadratic trials.

## Restriction-stable oracle and bisection

The required oracle takes a public target subset T and a contiguous subinterval [s,s+l) of [0,L), L=2m^2+2, and returns A(T,s,l), or a checked proper factor. Its cost must be bounded by soft O(m) uniformly over these restrictions; for example soft O(|T|+sqrt(l)) would suffice. Building the subset polynomial and the unit origin alpha^s must also be charged. A fast implementation of ONLY the one full-grid scalar does not automatically grant this contract.

Evaluate the full grid. Its gcd is nonunit by coverage. If proper, return it. Otherwise the product is zero modulo N. Split the target list in half, evaluate the left product and take its gcd with N. A proper gcd finishes. If the gcd is N retain the left half; if it is 1 retain the right half, whose product must still be zero modulo N because the left product is a unit. Repeat until one target remains.

Now split its index interval in half by the same rule. Every maintained rectangle has product zero modulo N. After O(log(m-1)+log L) calls, either a proper factor has been found or the rectangle consists of a single globally zero residual. The preceding sum theorem recovers p,q from that leaf. All subintervals are exact, with endpoints inherited from the original interval; no padded collisions are used.

This bisection does not assume simple roots, individual nonzero residuals, or prime local orders. Mixed-index saturation is resolved by the splits. Inversion is unnecessary: gcd=1 is used only as a mathematical unit test. With per-call soft O(m), total query acquisition stays soft O(m). Gcd, modular powers, exact square roots and the logarithmic controller add only polylogarithmically many operations on O(log N)-bit integers. Streaming storage can remain bounded by the oracle's storage plus soft O(m) target data.

## Native provenance

- SemiprimeDenseRowCarries.seedRow: original t=1 positive row.
- SemiprimeDenseRowCoverage.row_index_exists: exact integer factor index.
- SemiprimeWideWrapCoverage.post_prefix_factor_bounds and seed_index_bounds: arbitrary-ratio p<=m^3, q<=m^4 and 0<=I<=2m^2+1.
- SemiprimeQuotientRows.quotient_row_power_hit: original Fermat collision with exact source coefficients.
- SemiprimeGlobalPhaseCancellation.seedOffset_bounds and long_global_order_bound: short offsets and D>16m^4.
- SemiprimePhaseSumRecovery.integral_global_phase_sum: earlier general integral-phase mechanism.
- SemiprimeSeedSumAcquisition.seedLength_bounds, common_seed_sum_exact, long_seed_reader_witness, scanSeedSums_complete and long_public_route_seed_batch_succeeds: ALREADY compiled larger-range first-current coverage, every-global-hit sum identity and original complete long-branch reader; these are the most directly relevant historical endpoints.
- SemiprimeStrassenPrefix.prefix_none_excludes_small_prime: prefix failure excludes p<=m^2.

The existing larger full-stream arithmetic recovery theorems remain valid. The canonical seed source and its arithmetic recovery were already identified in the compiled historical endpoint. The simplification here isolates a restriction-stable scalar-oracle bisection controller for that same source. The unpaid task is its restriction-stable near-linear acquisition and complete all-branch bit accounting, not a new bounded-prefix coverage theorem for these uncentered seeds.
