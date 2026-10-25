# Full sixth-rate controller audit — 2026-10-22

Read-only repository audit. No frozen entry or repository file changed. The target is deterministic semiprime factorization in soft O(N^(1/6)) **bit** operations, rather than a query in isolation.

## Main conclusion

The strongest existing mathematical controller has already paid the public preparation and all exceptional order branches. For the original canonical scalar source, one restriction-stable soft-O(m) collision product algorithm would complete a classical deterministic all-semiprime sixth-rate proof by composition. No separate assumed primitive-root, factor-order, balance, QRH or gamma-acquisition premise is necessary on that route. The integration into the existing Lean controller and a complete Lean bit-cost theorem are still absent. This is distinct from saying that the current scripts implement this full pipeline.

Authoritative paid composition: `docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md` (below abbreviated U), lines7–80 and148–159. Its claims are independently reviewed classical bit algorithms, explicitly not an already compiled Lean backend (U26,72,118,159).

## Preparation is a proved paid algorithm, not a supplied-order promise

Choose public m with N<=m^6 and m=Theta(N^(1/6)). Parity and integer-square tests discharge even semiprimes and prime squares. If B=16m²>=N−1, trial division through sqrt(N)<=4m+1 is affordable (U28). Otherwise Harvey–Hittmeir's deterministic large-global-order algorithm supplies a factor or alpha with ord_N(alpha)>B in soft O(sqrt(B)) bits (U22). Removing the two-primary parts takes ceil(log2 N) squarings (U32).

The universal first-nonunit monic detector costs soft O(sqrt(B)) and returns a proper factor, both local orders>B, or their **exact common** order c (U23,34–40). In the last case, gcd checks along alpha^c's squaring chain either split the two valuations or compute the full common order r>B. Because r³>4096N and P+Q<r², `(N+1) mod r²` is exactly the factor sum (U42–58). This is a fully constructive closure, not order factoring.

Set beta=gamma^(N−1). Native projected-order arithmetic gives coprime local orders (U64). Screening beta either factors, retains two odd coprime orders>B, or gives beta=1. Only in the latter branch the algorithm **computes** a valid global annihilator K=N−1 of the original gamma and invokes the paid unbalanced short-annihilator extractor (U66–70). A final q=beta^(m²) screen either factors or certifies both q orders>B; its saturated common-order branch is impossible (U76–80). No numerical local order is supplied or output.

The extractor used here is **unconditional**, not QRH: `.../reports/unbalanced-extractor.md` lines7–9,25–29,31–41,59–70. It applies Burgess/Lau–Wu to cubefree Jacobi modulus and prime Legendre moduli; its cost is soft O(N^(31/192))<soft O(N^(1/6)). The deterministic trial fallback runs on only finitely many promised inputs; the theorem does not give a numerical effective Burgess threshold. This distinction must remain explicit in an executable endstate.

A literal reference extractor exists at `scripts/probe_semiprime_sparse_residue_gauss.py:203–271`: verified nonzero K, dyadic bins, public Jacobi scan, first-power screen, and total trial fallback. It does **not** acquire its input alpha. The catalog wrapper takes alpha as an argument (350), records `order_promises_checked=False` (375–378), and has conditional residue coverage. It is not the full public-preparation implementation.

## Source, localization and recovery already suffice

U92 charges public prime-m selection; U94–118 gives the original own-tag identity for the **new prepared beta**, without balance. The original window has L=2m²+2. U122–126 pays all O(m) targets, public integer-offset deduplication and all necessary same-side unit promises. Cross differences must remain allowed nonunits.

A proper leaf gcd factors immediately. A saturated leaf at i<4m² obeys the exact factor-sum identity P+Q=1+m²i−delta, because the prepared global order exceeds256m⁴ while the possible integer error is smaller (U132–144). This handles any colliding public row, not only the unknown own tag. It requires no long-annihilator QRH decoder. Do not replace this bounded index/offset ledger with an unbounded transformed leaf without proving its own recovery bound.

The sufficient query is precisely U148–155: exact product of original scalar differences on a supplied row subset and common seed subinterval, or a proper factor, in soft O(m) bits per call. A saturated product is localized by row and interval bisection in O(log m) calls; a unit child is discarded and a saturated child retained. A scalar zero without restriction/witness guarantees is insufficient. Complete antipodal-pair groups also suffice if their original paired products are actually acquired; after pair localization, two original scalar row descents close recovery. Unit Gauss aggregates, mixed-component norms, and complete twist fibres are not such a query.

For dyadic m, the new scratch `dyadic-native-interface.md` proves the corresponding actual integer row source and bounds for all odd tags, retains exact odd local orders under q=gamma^(m²), and handles centered midpoint carries. It is a mathematical extension, not an already compiled replacement of prime-m Lean source. Keeping the prime-m controller as fallback avoids making this extension a separate prerequisite of a universal theorem.

## Formal/controller boundary

`RiemannGaussian/SemiprimeSeedLcm.lean:284–301` proves N-only factor-or-large-order routing; `publicRoute` is declared **noncomputable**. `SemiprimeLocalOrderRouting.lean:263–283,324–335` similarly defines noncomputable refinement/routing and proves factor-or-kernel-or-long coverage. The theorem has explicit above-cap order hypotheses at the refinement boundary; it is not a stand-alone executable bit theorem for the newer beta composition.

`SemiprimeSeedSumAcquisition.lean:450–478` proves successful original long-route seed-batch recovery, but its projectedUnit/LongData wrapper is the older controller, not automatically the new beta. Its actual explicit source has O(m^(3/2)) size (`:511–532`) and a proved representation-specific superlinear floor (`:534–563`). Those are source counts, explicitly not full factoring bit-cost bounds. They cannot be quoted as a sixth-rate acquisition implementation.

The wider compact-GAP route genuinely has a different recovery interface: `docs/research-evidence/semiprime-acquisition-checkpoint-20261016/reports/group-gap-criterion.md:11,83,107` imports a QRH long-annihilator decoder, charging supplied annihilator bitlength. That analytic assumption and the requirement to acquire a nonzero certificate belong to that route. They should not be imported into the unconditional canonical bounded-leaf composition, nor silently removed from the wide-certificate route.

## What effort now closes the full endstate

1. Mathematical bottleneck: construct an exact, deterministic, restriction-stable ORIGINAL-source query in soft O(m) bits; include initialization, all carries, zero divisors, saturated hits, and source recovery. The known general query remains soft O(m^(3/2)) (U159). A single unrestricted aggregate without localization does not close it.
2. Separate integration task suitable for parallel work: state and stitch the already-proved classical public setup, query, and bounded-leaf decoder into a single explicit controller with a residue-bit ledger, then transport the new beta (or dyadic) coverage into Lean. This is important endstate work, but should not be presented as an independent unsolved number-theoretic preparation problem.
3. For an actual verified implementation/theorem, replace noncomputable choices and unpriced primitive interfaces by executable algorithms with proved bit bounds. Existing probe correctness/control tests do not establish asymptotic Python/GMP complexity. Modular powers and gcds are polylog-bit operations, monic product/MPE trees must be charged, and every query recursion contributes only logarithmically many calls.

Thus no new analytic assumption is needed merely to finish the bounded canonical route. If the eventual construction instead outputs a much longer or only local annihilator, its decoder contract and analytic assumptions must be audited anew. No claim here proves the missing query or the complete Lean sixth-rate theorem.
