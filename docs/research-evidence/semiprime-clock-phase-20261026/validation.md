# Validation of the amended parity cover

Run the public constructor and separate exhaustive validator from the formal repository root:

    python3 docs/research-evidence/semiprime-clock-phase-20261026/check_parity_cover.py --output /tmp/parity-cover-replay.json

The default three fixtures use e=3,4 at balanced public bins and e=3 at an axis bin, with N=K^6-1. They are arithmetic metadata fixtures, not prepared semiprime instances. They exercise both nonaxis phase classes and the changed 2K axes.

The constructor enumerates the enlarged ellipse with the parity condition, acquires its complete stationary colour fibres, selects the sparse support partition and emits the public parity, shifted root exponents, common base exponent 2H and clipped length of each row. Its constructor-only path is available with --no-validate. The optional padding flag explicitly requires a later numerical endpoint unit gate; no group value or gate result is fabricated.

The validator independently evaluates each row polynomial modulo H at every unit colour. It compares those actual root sets with the acquired phase classes and selected partition. For both lifts R=r and R=r+K it constructs S=N/R modulo 2H and checks the clock parity directly against the public formula. Its exhaustive support work is O(K^2) and is separate from the soft-K constructor.

The recorded run passes 11,088 direct support checks, 3,204 selected-support checks and 608 parity-lift checks. A separate root replay has identical output after removing only the three wall-clock timing fields. The constructor-only path was also exercised. These finite diagnostics detect arithmetic and metadata mistakes; the uniform cover, order margins, endpoint gates and complexity claims are paper arguments in parity-cover-audit.md.

The independent recurrence review checks the alternating sign, paired transfer, polynomial antidifference, finite Euler tail and composite-ring validator. Its two requested scope clarifications were applied and reread. The independent knot-source review checks the finite character response and its coordinate-only decoder, including the published cyclic-dilogarithm correction. No Lean build, factor-field experiment, factoring-success campaign, commit or push is part of this validation.

The symmetric-character review independently checks the gauge, reciprocal fold, Dixon specialization and its precise coefficient match. Its initial primary-PDF fetch timed out. Root subsequently downloaded Chu's primary PDF and checked printed page 132, equation (1), both in extracted text and in a rendered page; it agrees with the formula used in the report. Root also reopened Okada's primary paper and checked the stated Q-function generating and Cauchy identities. A separate final integration review passed the README's distinctions between public row parity, an unknown global collision phase, a constant horizon gain and the missing exponent improvement.
