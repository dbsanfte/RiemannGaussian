# Public gamma generation and remaining whole-controller cost

2026-10-15. Read-only inspection. Sources pinned in native-pins.json. This is a status/provenance report, not a new cost theorem.

## Gamma generation does not request an unknown large order

The compiled matched-width controller is SemiprimeWrapIndexRecovery.routeAtRowModulus. It computes publicRowModulus N, runs SemiprimeSeedLcm.routeByWidth at that width and refines an above-cap seed with SemiprimeLocalOrderRouting.refineBase. routeAtRowModulus_semiprime proves the actual public output is a proper factor, a certified kernel base or a certified long base. No large numerical group order, hidden factor or advised generator is input.

SeedLcm.seedChoice tests public integers 1,...,M+1 for nonannihilation by the maintained small common modulus M. The loop maintains M<B until its progression branch; a clear small-order seed extends M by LCM and at least doubles it. logarithmic_setup_budget bounds the actual number of seed candidates by B*clog(2,B) and bounded-collision records by 4B*clog(2,B). Only bounded seed orders, not the final D>16B^4 order, are acquired/peeled on this path. Consequently a generic sqrt(D) order-finding charge on the final gamma is not the cost of this controller.

RefineBase performs a short-order batch on the selected seed; if clear it checks g^(N-1). A kernel gives a different certified branch. Otherwise a public staged projection is checked and followed by another short-order batch. Failure supplies LongData. The projected unit is

gamma=(g^(N-1))^((B!)^clog(2,N+1)).

The exponent need not be written out and exponentiated in one large integer operation. StagedSeed.publicStage and its equality theorem implement the public factorial projection by successively raising the raw unit to i^clog(2,N+1), for i=1,...,B. The successive small exponent lengths give an ordinary soft O(B) arithmetic schedule at polylogarithmic operand size; this schedule alone is not the complete controller bit proof.

LocalOrderRouting.refinementGcdCount_le and refineBaseGcdCount_le give <=9B+1 and <=9B+2 added gcd queries. LongData includes coprime B-rough local orders exceeding 4B^2 for the projected unit; GlobalPhaseCancellation.long_global_order_bound then derives D>16B^4 as a theorem, without finding D numerically.

## What is actually certified, and what remains unpaid

The source controllers are noncomputable Lean definitions using classical list/search/group abstractions. Their arithmetic correctness and source/query counts are compiled; they are not a complete uniform bit implementation. The seed-LCM audit and local-order-routing audit explicitly set is_bit_complexity_certificate=false. Their historical limitation fields are older checkpoint statements; current later kernel/seed recovery endpoints must be considered separately.

SeedLcm.logarithmic_setup_budget counts seed candidates and baby/giant records. It explicitly leaves sorting, trial factorizations, order peeling, gcd recovery and polynomial arithmetic as separate charged categories. CollisionPeeling.peelOrder must be implemented/charged for the bounded annihilators encountered. LocalOrderRouting's 9B+2 theorem counts gcd queries only; it explicitly excludes a certificate for the polynomial or bit backend. The staged projection has exact value and gcd-count endpoints, rather than a complete composition with seed selection and all bit primitives.

Kernel outcomes are not secretly counted as long outcomes. KernelDescent.publicTrace_cases certifies either an original proper factor or transport from a certified projected-long leaf after kernel residual descent. publicTrace_width_budget and publicTrace_routing_width_budget bound total source width by O(B log N); their comments expressly exclude complete polynomial/bit costs. Kernel residual splitting, factor transport and adaptive controller costs remain part of the whole-run implementation obligation. The canonical long-query reduction does not itself implement these other branches.

There are later local bit arithmetic, power-walk, inverse, geometric and index-reader modules, but their existence must not be promoted to a composed every-run theorem for the entire route. The journal repeatedly distinguishes those local clocks from setup/routing/descent and full every-run memory/bit accounting.

## Correct conditional conclusion

Given an ACTUAL certified long outcome, the canonical first-current source has native coverage and native sum recovery. A new restriction-stable scalar query primitive would give a simple logarithmic-call recovery controller on that branch. This does not by itself prove the requested all-semiprime deterministic N^(1/6) bit bound: seed setup, projected/kernel branch implementation, bounded order peeling, all arithmetic backends, recursive composition and peak memory must also have the required charged bounds.

Conversely, it would be inaccurate to say that obtaining the long certificate necessarily costs sqrt(D) with D>16B^4. The public controller derives its long-order lower bounds by failure of bounded tests and exact projection identities; it does not numerically compute that large order.

## Most relevant retained endpoints

- SeedLcm.routeByWidth_semiprime, publicRoute_semiprime, logarithmic_setup_budget.
- LocalOrderRouting.refineBase_semiprime, publicRoute_semiprime, refinementGcdCount_le, refineBaseGcdCount_le.
- StagedSeed.publicStage_eq_projectedUnit, checkedProjection_gcd_count.
- WrapIndexRecovery.routeAtRowModulus_semiprime.
- KernelDescent.publicTrace_cases, publicTrace_width_budget, publicTrace_routing_width_budget.
- SeedSumAcquisition.common_seed_sum_exact, long_seed_reader_witness, long_public_route_seed_batch_succeeds: original m-1 seed arithmetic source/recovery already compiled before this turn.
