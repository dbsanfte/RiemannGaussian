# Independent exact-file uniform-preprocessing review

2026-10-16. Verdict: PASS; no correction requested.

Exact reviewed target: `uniform-preprocessing.md`, 8770 bytes, SHA256 `375460025deb024f03c3bc3415fc7990ca9a50b16cc9e272a19b17dd08d2e4fd`.

I read the complete final proof and checked its algebra against the independently proved small-order separator and my earlier preprocessing audit. This is a classical proof review, not a new Lean/build certificate. Harvey--Hittmeir Theorem 1.1 is an explicitly identified external algorithmic premise; the present review does not reprove that theorem.

Section 1 correctly respects the large-order theorem's B<N-1 input range. When B>=N-1, sqrt N<=sqrt(B+1)<=4m+1, so explicit trial division has the stated affordable soft O(m log N) bit cost. The fallback requires no unknown finite threshold.

Section 2's detector is valid WITHOUT an order-size promise. Row coverage and right-first localization prove either a proper factor, exact equal local orders at the earliest saturated leaf, or BOTH local orders exceeding H². Repeated points and zero divisors are harmless under monic remainder evaluation. The sibling degrees sum to O(H), and the H row gcds fit the soft bit bound.

Section 3 uses integer H=4m, so the tested cap is exactly B. The 2^ceil(log2 N) projection removes every local 2-part. NoHit therefore supplies both large odd orders, and P,Q<=P+Q<=3m³ proves both indices below 3m/16<m. No prime-order assumption is introduced.

Section 4 correctly obtains the exact pure-2 local orders of alpha^c. A differing 2-adic exponent forces a proper gcd before saturation, whereas first common saturation certifies equal exponents. The resulting r is the common FULL alpha order and hence its global order>B. Thus r² divides phi(N), while r²>B²>P+Q. The least residue (N+1) mod r² is exactly the factor sum, permitting exact quadratic recovery. The c=1 and initial chain stages are covered. A computed r² greater than phi(N) cannot arise in the common-order branch because divisibility has already been proved.

All subsequent powers, chain gcds, remainders and square roots cost only polylog N bits; the external search and H=4m detector dominate at soft O(m log N). No upper bound m=O(N^(1/6)) is needed for THIS displayed preprocessing bound. Such an upper bound remains necessary when a later theorem rewrites m-dependent work as an N-exponent.

Section 5 correctly handles arbitrary composite odd output orders, including shared factors with their indices. The direct identity (a^Kodd)^v=1, since r divides Kodd and rv=P-1, proves the small-order property without a coprimality cancellation. The conclusion is precisely an order/index interface or factor. It explicitly does not transfer the original base-specific collision coverage, assert a global m^4 order bound, acquire an annihilator, or complete the full-query/Lean controller.

No mathematical blocker found in the exact file.
