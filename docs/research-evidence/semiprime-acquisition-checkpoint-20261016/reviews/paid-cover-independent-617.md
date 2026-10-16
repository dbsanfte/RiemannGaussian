# Independent review of paid compact-GAP order-cover transfer

2026-10-16. Reviewed report SHA256 782c39a8e1eaa5a32b03cfcf2f6f61561aa3595d20c2dbd9cc7deb0ee856f644.

Verdict: PASS as a conditional constructive transfer, with the size conventions below made explicit. It does not acquire the cover or prove UW conjectural coverage.

1. Explicit product interface is correct. If one whole local order divides the integer product, gamma^K-1 has nonunit gcd with N. A proper gcd solves factoring; saturation supplies a genuine nonzero global annihilator. Product-tree cost is soft O(total input bits), including its output length. Product divisibility does not need a termwise local-order hit.

2. Structured cross-difference interface is correct under INDIVIDUAL difference coverage. A covered pair makes one modular-power difference nonunit. Monic subproduct/remainder trees over Z/NZ do not require invertible node differences or distinct residues. At a saturated row, descend a balanced T tree: evaluate the left child; proper gcd factors, gcd N retains that child, gcd 1 retains the other nonunit child. The sum of sibling degrees is O(V_T). Thus one leaf, not a list of repeated candidate leaves, suffices. Saturation at that leaf yields gamma^(s-t)=1 modulo N. The certified integer inequality s!=t is essential.

3. Enumerate PARAMETER BOXES as multisets. Duplicate sums/powers cause no correctness problem, but cardinalities and work must use V_S+V_T, not the possibly smaller sumset sizes. Keep a single ordinal label per generated residue; a full c-tuple need not be stored at every point. At the final leaf, recover its mixed-radix coordinates in polylogarithmic overhead. Precompute powers for each step and its wrap/reset, after combining all starts. A mixed-radix traversal needs O(V) modular multiplications: remove length-one coordinates, then each active coordinate has length>=2 and the total number of carries is bounded geometrically by 2V. Starts, steps, and reset exponents are paid.

4. Bit-size precision: if D bounds only the bits of input starts and steps, an enumerated exponent may have D_eff=O(D+log(V+1)+log(c+1)) bits. Reset exponents have the same bound. Use cD_eff in the construction/recovery clock, or define D from the start as a bound on the generated hull exponents. For polylogarithmic rank and V=soft O(m), this distinction does not change the proposed soft O(m) conclusion. A declared D-bit input without this adjustment should not be used as an exact generated-exponent bound.

5. Cheap zero avoidance: write each GAP as a+sum_i k_i d_i, 0<=k_i<L_i. Its exact hull extrema are

 lo=a+sum_i min(0,(L_i-1)d_i),
 hi=a+sum_i max(0,(L_i-1)d_i).

These are computable in soft O(cD_eff). A certificate lo_S>hi_T (or lo_T>hi_S) ensures every cross-difference is nonzero, including overlapping parameter descriptions. This is a sufficient certificate, not a necessary condition. The COVER CONSTRUCTION must already supply a separated pair; arbitrarily shifting one GAP to force separation need not preserve its divisor coverage. The transfer makes no such shift for free.

6. With gamma's odd local orders>B and a recovered nonzero global annihilator of D_eff bits, the reviewed QRH decoder contributes soft O(D_eff+N^(1/12)). All modular powers, hull checks, enumeration, selected-exponent recovery, polynomial work and gcds are therefore within

 soft O(cD_eff+V_S+V_T+N^(1/12))

in addition to constructing and reading the supplied cover. Negative exponents use one paid inverse of the given unit. This is soft O(m) under the report's paid parameter bounds. No prime modulus, local order, factorization, or auxiliary-prime oracle is used in this consumer.

7. The gap between interfaces is correctly identified. If a composite local order divides a PRODUCT of cross-differences but no individual difference, the monic modular-power batch need not have any zero modulo that factor. One must either materialize a paid short integer product and use interface 1, or supply strong/individual coverage for interface 2. The construction does not silently transfer UW's weak product property to strong coverage.

The report's conditional all-input consumer is useful. It remains conditional on constructing the separated, individually covering compact GAPs with actual box volume and description/bit cost inside the budget. Neither a conjectured n-divisor cover, a sumset-cardinality assertion without enumeration cost, an n^(1/3+o(1)) bound, nor an infinitely-many-scales existence statement supplies the stated soft O(m) acquisition for every N.

## Final exact-criterion pin review

Read the full `group-gap-criterion.md`, SHA256 `6fb196a7d87a81a53e1169810044fa5a946f85f683f79b25f2498e648929a5c9`. Verdict: PASS. Its explicit D_* = D+ceil(log2(1+cV))+3 incorporates the generated-exponent correction above. It proves hull checks, actual-box enumeration, ordinal recovery, monic localization, strict positive K, and one QRH decoder call with the correct total soft O(cD+V+N^(1/12)) charge. Signed steps and length-one coordinates are handled, and repeated parameters/residues are allowed. The individual-cross-difference cover remains an explicit proved-input promise, with no conversion of weak product coverage and no claim of a constructed universal UW cover. This review and its source pin are now frozen.
