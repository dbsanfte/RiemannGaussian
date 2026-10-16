# Independent review A: all-semiprime setup and remaining query

2026-10-16. Verdict: PASS for mathematical correctness, stated classical bit clock and source attribution. No repository edits, builds or new compiled theorem are asserted.

## Exact targets and source checks

- `uniform-setup-and-query-interface.md`: 13939 bytes, SHA256 `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`.
- `setup-query-source-pins.json`: 2056 bytes, SHA256 `2c790a49f7aabb174ee19fd82a935c3ea0144ae8e988ed0d9b93280c21d6e225`.
- Invoked final `unbalanced-extractor.md`: 9993 bytes, SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.

Independently verified raw length and SHA256 of all nine setup metadata dependencies. Read the relevant native statements/proofs: SemiprimeOrderSeparation.projected_orders_coprime; SemiprimeWideWrapCoverage.seed_index_bounds; SemiprimeSeedSumAcquisition.long_seed_reader_witness; SemiprimeQuotientRows.quotient_row_power_hit and centered definition. These are arithmetic-source inspections, not fresh Lean compilation. The prior HH primary contract and the separate dyadic extractor are used with exactly their stated inputs.

## All-input setup

HH is called only for B<N-1. Otherwise sqrt N<=sqrt(B+1)<=4m+1 makes trial division affordable. Raising alpha by 2^ceil(log2 N) removes every local two-primary part without altering the odd parts. The universal detector's exact common-order output is stronger than an lcm and its use is legitimate for arbitrary composite local orders.

In the common-odd-order branch alpha has local orders c*2^a_P and c*2^a_Q. The squaring/gcd chain factors if the valuations differ and otherwise computes the exact common full order r>B. Then r² divides phi(N). Both factors are at least r+1; because P<=sqrt N and x+N/x decreases there, P+Q<=r+1+N/(r+1). From r³>4096N and r>64, this sum is strictly below r². Thus (N+1) mod r² is the exact positive factor sum. Neither balance nor a factorization of r is needed. This closes the previously balance-dependent numerical step correctly.

The N-1 projection invokes the existing coprime-order arithmetic, not a prime-order assumption. A common projected order is consequently one, giving the explicit valid K=N-1 for ORIGINAL gamma. The new dyadic extractor applies because original gamma has both odd orders>B; no small-index promise is imported from the old balanced theorem. Its N^(31/192) bound is below the target N^(1/6). Otherwise the odd coprime beta orders both exceed B, so their product is the global order and exceeds B². Applying the detector to q=beta^(m²) either factors or certifies both q-orders>B: the common-order-one case would force both beta orders to divide m². This argument needs no gcd(m,order) condition.

A fixed number of soft-sqrt(B) detectors, HH, polylog-bit exponentiation, and at most one new extractor invocation has soft O(m) total bit cost. The even and square preliminary branches are valid for semiprimes. The theorem does not extend these statements to arbitrary composite shapes.

## Native canonical coverage without prime orders

The literal row formulas agree with the native denominator-one construction. The own-tag integer index comes from its quotient relation and satisfies the displayed identity N+delta-m²I=(P-1)(Q-a). The native seed_index_bounds theorem at line147 requires only m>1, P<=Q, P>=m², N<=m6 and the exact index equation. Its proof uses P<=m³ and Q<=m⁴, not balanced factors or local prime orders. The present surviving branch supplies the stronger prefix P>B. Hence I lies in [0,2m²+1] and the proposed L=2m²+2 covers it. Native quotient_row_power_hit requires only the local Fermat period. It therefore applies mathematically to the new beta. The source correctly distinguishes this arithmetic transfer from automatically compiling the projectedUnit/LongData reader/controller for beta.

Public prime m selection by deterministic primality tests and Bertrand search costs soft O(m) bits, with fixed polylogarithmic costs per O(log N)-bit candidate; gcd(m,N) is a legitimate factor branch. Constructing all literal rows and target powers similarly costs soft O(m). Signed powers are safe because beta is a known unit.

## Unit promises, global leaves and scalar interface

The literal offset interval [-3m²,m²] follows from canonical a and centered b. Different integer offsets differ by at most4m², below each local beta order. They therefore give targets distinct in BOTH fields, so pairwise target differences are units. Equal offsets are publicly deduplicable. The short seed differences and q-factorials are units by the separately certified q orders. Cross target/seed differences are deliberately allowed nonunits; no inversion of them is licensed.

The unbalanced surviving factor-sum margin is valid: both primes>B+1 give P+Q<=B+1+N/(B+1)<16m²+1+m⁴/16. The retained coprime local orders imply D|phi(N); this divisibility would not follow merely from a large arbitrary global order, but the report has already proved coprimality. A globally equal bounded leaf also gives D|(N+delta-m²i), hence D|(P+Q-1+delta-m²i). Its stated safe absolute bound is below256m⁴<D. Therefore P+Q=1+m²i-delta exactly, for every such global leaf, and a square root factors N. The proof does not need the private own tag or prime local orders.

The scalar product contract is sufficient ONLY with its explicit restriction stability. Initial nonunitness follows from the own collision. Saturation is localized through binary row and common-interval restrictions: proper gcd terminates; a unit child can be discarded; otherwise retain a saturated child. Each step needs at most two restricted calls, and only O(log m) levels occur. A saturated singleton is the bounded global leaf above. Thus a uniform soft-m restricted scalar evaluator would give soft-m total factoring, including source acquisition. A single unrestricted norm value zero does not provide that contract. The report states this distinction correctly.

## Remaining scope

This is a paid all-semiprime setup plus inherited canonical arithmetic coverage and a precise sufficient missing evaluator interface. It proves neither that evaluator nor any improved general query bound. The existing soft O(J+sqrt(JL)) cost remains soft m^(3/2). No original-controller bit theorem or full Lean sixth-rate objective is claimed. No operation lower bound, balance assumption, small-index assumption or prime-local-order premise is silently imported.
