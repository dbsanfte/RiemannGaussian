# Independent final review B: unbalanced extractor and all-semiprime query interface

Verdict: PASS, no correction requested. This is a read-only classical proof review, not a new native/Lean build or formal controller certification.

Exact reviewed targets:
- `unbalanced-extractor.md`: 9993 bytes; SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.
- `uniform-setup-and-query-interface.md`: 13939 bytes; SHA256 `4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`.
- `source-pins.json`: 1749 bytes; SHA256 `7c6cd53d7348a12ea34ea48eb539dfa7199292d5429e0b1513a853e3f2895553`.
- `unbalanced-extractor-review-a.md`: 3784 bytes; SHA256 `8c5b6f983dfda556ecddcf4a64692cee1375ebee533da1254a8577bbb715387c`.

The existing extractor-review-a pins the final 9993-byte extractor. I independently reread that exact file and retain its PASS conclusion: one small local order suffices; the correct public power-of-two bin always guarantees a hit; wrong-bin NoHits/common outputs are safe; Jacobi-minus equality proves unequal field 2-adic valuations; the correct-bin nonresidue trial separates them. Rounded Y_X and caps preserve the worst-bin N^(31/192) bound with m=Theta(N^(1/6)). The uniform Burgess statement is correctly about the character bound, with success required in the correct bin only. Fixed finite fallback and the K=0 guard are explicit. Arbitrary composite odd local orders, index overlap and polylog-bit K cause no algebraic or cost gap.

For the all-semiprime setup, Sections 1-4 correctly retain HH's legal target range and affordable explicit trial-division branch. Common odd gamma order is resolved through the pure-2 chain. The computed common full order r>B gives r²|phi(N), P>=r+1 and r³>4096N; monotonicity yields P+Q<=r+1+N/(r+1)<r² WITHOUT balance. The N-1 projection is inherited native coprimality arithmetic. Its common-order-one branch acquires K=N-1 for the ORIGINAL gamma and invokes the UNBALANCED extractor, not the old small-index theorem. Surviving beta and q detectors provide both long local orders, coprimality, strong global order and every specified short scalar unit. No numerical order or factor advice is used.

Section 5's unbalanced factor-sum bound follows since both primes exceed B+1. I checked the native seed_index_bounds statement and the arithmetic portion of long_seed_reader_witness directly: their hypotheses are the post-prefix smaller-factor bound, ordering and N<=m^6, not factor balance or prime local orders. Thus Section 6's generic-unit use is mathematically legitimate. The explicit identity N+delta-dI=(P-1)(Q-a) proves an own-tag hit for ANY beta unit. The text correctly notes that the compiled packaged theorem still carries its old wrapper; no automatic beta-controller formalization is claimed. Prime selection and prefix checks are charged.

Targets, integer-offset deduplication and powers are softly linear. Distinct offset differences are smaller than BOTH certified local beta orders, so target differences are units in both fields; q-seed differences and q-factorials are also legal. Cross target/seed differences deliberately remain allowed nonunits. No long-degree coefficient vector is silently acquired.

Section 8 correctly derives D|(P+Q-1)+delta-di. The displayed unbalanced sum margin, offset band and bounded i put its absolute value below D, forcing exact zero and recovering the factor sum for ANY global leaf, including a public false tag. This needs neither original-base2-specific local orders nor a private factor tag. The exact phase-sum mechanism is inherited and credited.

Section 9 states a sufficient RESTRICTION-STABLE query, not an acquired one. Canonical coverage forces the full product nonunit. Proper gcd terminates; saturated products can be localized by row then common-interval bisection in O(log m) calls; a saturated leaf invokes exact sum recovery. A naked zero full norm lacks this witness guarantee. Ring work and residue-bit costs are expressly charged. Empty products, deduplicated rows and actual nonunit cross differences are handled. The unchanged general soft m^(3/2) acquisition bound is accurately reported.

The substantive extension is paid same-input setup plus a precise remaining sufficient query interface for every semiprime, with even/square preprocessing stated separately. It is not a new projection identity, first algebraic kernel closure, obtained long-query evaluator, full one-sixth factorizer or new Lean theorem. No remaining proof/scope blocker found.
