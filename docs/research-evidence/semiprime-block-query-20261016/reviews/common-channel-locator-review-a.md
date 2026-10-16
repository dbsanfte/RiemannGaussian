# Independent common-channel collision-locator review

2026-10-16. PASS on the stated actual hidden-field scope. No report mutation or new computation claim.

Exact target: `/tmp/semiprime-decimation-query-20261015/source_additive/common-channel-collision-locator.md`, 4385 bytes, SHA256 `6dfc707ebe2896d7eb2ff78b6324d4df78b3db7ca6bc6a3e67e7b4adf4c737ff`.
Exact prerequisites rehashed:

- block_transform/report.md: 8629 bytes, `825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70`.
- decimation/report.md: 10005 bytes, `65a5c827a64b5c035d3d0a7bed445c6970910f9f92749309878d1e1520e5c4fd`.

All seven distinct direct source-pin paths appearing in those two manifests also match their recorded hashes and lengths. This review uses the inherited reviewed local-order/density premises; it does not independently rebuild the analytic supply or claim new primary-literature inspection.

The proof is correct. In either actual hidden field the characteristic is odd, so B=2^k is invertible, nonzero fibers of t->t^B have B distinct roots, and primitive B-th roots exist in an algebraic closure. A standalone abstract version must retain this characteristic condition: an odd-order subgroup alone would not suffice in characteristic two. The current actual-field scope already supplies it.

F has simple roots q^(-i) in the odd-order subgroup because L is smaller than the q-order. The mask roots are exactly the B-1 nontrivial dyadic phases of each distinct z_j. Equality between two such roots forces the same phase and same node: the intersection of an odd-order subgroup with the dyadic roots of unity is {1}. No mask root is in the odd subgroup. Thus F and E_B are coprime and their product is squarefree with constant coefficient one.

The divisibility equivalence A(Y)|N_r(Y) for every r iff A(t^B)|F(t)E_B(t) follows from the free basis 1,t,...,t^(B-1) over K[t^B], or monic division. For a nonzero common root xi, its complete fiber must therefore be contained in the roots of FE_B. Any fiber containing an F or mask root contains one unique odd-subgroup point. If that point is a supplied z_j, the mask gives precisely all B-1 remaining points and completeness requires F(z_j)=0. If it is not supplied, there are no mask points in its fiber and F supplies at most its one odd point; B>=2 makes the fiber incomplete. A fiber with no odd point contains no F or mask root. Zero cannot be common because N_0(0)=1.

Every complete fiber is simple in FE_B. Since B and its nonzero roots are separable, a repeated root of the channel gcd would induce repeated roots of H(t^B), impossible. The gcd is therefore exactly the displayed monic product of distinct powered collision nodes, with no hidden extra factors or multiplicities. The powered nodes are distinct by dyadic injectivity on the odd subgroup.

This is a genuine zero-selective polynomial observable. The retained unit-row density implies only o(m) collision rows in either field, hence the inherited degree bound on its locator after deduplication. It does not imply sparsity of the locator coefficients. The fieldwise locators need not have the same degree or admit an immediately licensed monic polynomial-gcd computation over Z/N. A composite algorithm requires paid leading-coefficient/pivot and proper-factor/saturation handling, exactly as the report says.

The arbitrary-point channel-vector oracle is fully paid by the new block transform, including collision-bearing arguments and without normalizer inversion. However it supplies a vector of VALUES at one point, not polynomial coefficients or a polynomial gcd. A generic interpolation route still needs Theta(J) such evaluations in the degree-O(J) family. The report does not claim this is a lower bound for its structured family.

No nearlinear black-box common-gcd acquisition algorithm was identified in this review. Two random linear combinations could be a candidate gcd representation, but their polynomial coefficients and factor-safe gcd remain missing, and a small common factor does not make their coprime parts low-degree. At an actual powered target, simultaneous vanishing of the channel vector is exactly the original row collision test by the unit transport formula; treating that predicate as already supplied for all targets would again skip the acquisition. These observations preserve the positive locator target rather than rule out a future structured or output-sensitive acquisition method.
