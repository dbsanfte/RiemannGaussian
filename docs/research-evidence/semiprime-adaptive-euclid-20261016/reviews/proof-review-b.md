# Final independent review: hyperbolic catalog and complete intermediate rays

PASS for BOTH exact final reports. The earlier minor native-threshold wording issue is resolved. No remaining correction requested. This review preserves rather than overwrites the old review.

## Exact targets and pins

- report.md: 14077 bytes, SHA256 242dbe88a63b516da5b659983f4dccf9c7b13cb805b5053cf7fc6e580cb62ca7.
- source-pins.json: 1277 bytes, SHA256 cf8528861d5d6537fa29dab869c8c82f67675820d5a62987b34aaf06e9a31f43.
- full-ray-trimming.md: 7771 bytes, SHA256 52684f92a92b2b037d687d99708ff3a3473c5b22502990686d308a9fdc902b23.
- full-ray-source-pins.json: 636 bytes, SHA256 afce9896d4405c1b80dc87f6213ca087c7bd6594354a709f02aaaee962462cc6.

All eight source-pin references independently match current sizes and hashes. The final report differs from report-v1-reviewed.md (14017 bytes, b7654d123cc40085532411af75194c9553a978580ca102597208ae563d7bc3f5) ONLY in the requested native-threshold phrase. It now distinguishes fixed-sqrt publicRow from nonzero outputs at other admissible positive thresholds. The earlier full review, review-b.md (6607 bytes, 9f533c659db1211ebea3756c179bff576e3502d4f4d6d27d55c3b5bdf44fc5fa), remains valid with that issue discharged.

## Hyperbolic theorem reaffirmed

Rechecked the final proof's catalog determinant count, explicit signed hyperbola enumeration, square-table lookup without root oracle, weighted color energy with duplicate field points, four-fourth-entry count, higher-digit averaging, selector telescope and exact constants. The softly O(m ell^2) bit setup is correctly conditional on supplied N,m,gamma and polynomial-size exponents; earlier gamma setup and long residual acquisition remain separate.

The global phase argument uses D>16m^4, S>12m^2 and S<=3m^3, with no local energy inference. The chosen-origin extension changes signed delta-sum bounds by at most 2H m^2 after cancelling a common translation; the two explicit range inequalities suffice. It protects arbitrary high-digit/factor advice without a union over choices because every selected exact equality injects into the SAME raw low-digit catalog. One chosen origin per source entry is essential to this argument; an uncharged union of shifted copies is not licensed. None of these representation bounds certifies collision coverage of an arbitrary advised selection.

## Complete native ray extension

Independently inspected SemiprimeEuclidRowFamily.euclidPairs/publicPairs/publicPackets and SemiprimeEuclidRowBudget.publicPackets_length_le. The deduplicated triple set is bounded by the compiled per-input packet LIST length, not by a universal coordinate-set count. Each source pair emits two centered packets, so the bound 8m L_m^2 is conservative. publicPairs depends only on the low input digit through quotientSlope.

For a proper intermediate, r'=r0-k r and t'=x+k y satisfy m=r t'+r' y with r',r,y positive. Therefore 0<r'<m and 1<=t'<m; current nonzero vectors satisfy the corresponding bounds. These facts, plus the compiled congruence, supply exactly the field-coordinate assumptions needed after occupancy control. The hyperbolic product condition is not imported for intermediates.

Heavy-tag counting is correct: more than B_m=64 L_m^4 distinct triples at a tag, against total <=8m L_m^2, gives at most m/(8L_m^2) heavy tags. The stated m>=5 inequality leaves at least 2m/3 light tags. This trimming is deterministic from n alone. At light tags at most B_m colors suffice, so the unchanged cone and high-digit proof gives sum_h E_light<=8 B_m^4 m^(7/2), with bad product residues <=8m^2/lambda.

The fourth-entry bound remains FOUR despite signed a: a fixed t and low delta give at most two j roots and at most two integer a representatives per j in (-m,m). Weighted duplicate field points are retained. The zero-slope reduction is to the same additive cone quadruples. Thus all high-digit/advised policies are bounded simultaneously; no independent randomness or generic specialization appears.

## Good subset versus full family

For one selected ray per original tag, restrict ONLY FOR THIS PROOF to the light tags. Exact global phase equality forces equal t and delta, and at most two selected tags share a target. Hence the light target SET has at least m/3 members and satisfies the energy bound. Every cover of the complete advised target set covers that light witness, yielding k^2 T>=m^(3/2)/(162 lambda B_m^4).

The report correctly does NOT assert the same energy upper bound for the full target union including heavy tags. Its full-union cover statement follows instead by containment of a selected light witness. This distinction is material. Nor is collision coverage claimed after trimming: a useful own-factor tag can be heavy. The source-set representation obstruction is not a trimmed factoring algorithm.

The extension's relative-origin clause is conditional on the SAME explicit range-H inequalities; polylogarithmic relative spans qualify eventually, and one origin per source entry may be chosen with full advice. Native publicShift/reflectedShift ranges are NOT automatically within that clause. Multiple origin copies need a separate occupancy/multiplicity charge. Covers of all native centered packet exponents with unrestricted center ranges are therefore not silently included.

## Supply, costs and remaining scope

The selector argument counts all original P and all current candidate m through the inherited varying-selector telescope, with one Q per bad residue per half-open width-m^2 box. It gives O(K_* M^6/lambda) against the SAME original qualified supply. The stated lambda condition and finite union with prior sub-six-power and separately invoked o(M^6/log^2 M) losses preserve majority size. No factor of the advice space, origins or number of policies is omitted; those choices are inside one deterministic raw-energy domination.

The complete list's explicit Euclidean generation, sorting/deduplication, occupancy labels and exact lifts have the advertised soft-linear public operation count and soft O(m ell^2) bit setup, using the compiled output budget and polylogarithmic per-entry arithmetic. This does not pay any long row product. Polylogarithmic candidate menus and the larger polynomial menu retain their distinct lambda/exponent costs.

Both final statements are global carrier-representation obstructions. They allow high-productset carriers, implicit/non-cover sharing, nonlinear norm and factor-only algorithms, tiny selected-tag subfamilies and unqualified large center ranges. Neither proves an arithmetic-operation lower bound, a new native theorem, a collision-complete trimmed source, or a sixth-rate algorithm. No original report, certificate, native file or frozen packet was edited for this review; no build or numerical experiment was used.
