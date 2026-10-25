# Independent integration review: terminal-boundary packet

Verdict: PASS. No corrections required. No source, draft or shared repository file was edited by this audit.

Exact draft SHA256 pins:

* `journal-append.md`: `722929c68a8d50bdf2b123bcbb372ad10e75caf2836cdac478e0de4e789d41f6`.
* `agents-append.md`: `32f7095b5fb354e5566008708cc3a8ae40c5f3892f43de99a39fc60877e0ff5b`.

Exact source SHA256 pins:

* `boundary-solver.md`: `ffbc045a4e646c89b444ff3a2732f003660780a73b5cf44f7ce7df684529532f`.
* `adjoint-terminal.md`: `3a95f0ffd153bc2ab661fd5bb4a62b34a0d107f382d2ecaa41d75e6b3f78d8c4`.
* `newton-terminal.md`: `d4f59a31f8b7d92cfd3b2a91d4557bf7d98d0419bc4a6451c92e7ac47c6d9748`.

All three independent exact-source reviews are PASS. Their SHA256 pins are respectively `e66c8b7b11205f37315b8f32fe9b097492b2b2d4bd5c1890e004fc49329698cd`, `f945505935e9982b8ae4e03d6993881fcc296f45baef6e9a69ccbea0bf952f9a`, and `e3251de9a6d34985f4fb0ab46ef2e1f229dee9d4427c56238117a2b05ee94e8b`. This audit read the actual sources and reviews as well as computing the hashes.

The balanced setup is faithful: main L0=2H=k*(2k), reciprocal augmentation at q^(1-L0), and separately acquired original indices2H,2H+1. Both end vectors may be enlarged to O(j) width at soft-k cost by the actual power-sum construction; no middle vector is assumed. Reciprocal augmentation changes only constant degree factors and preserves the original product's support via known-unit squaring. Main reciprocal leaves retain index L0-1-i, while tail leaves retain their actual indices.

The extended denominator proof correctly uses k-rough component orders and actual q nonresonance, including split coordinates. Q=q^k has the same component orders, so Q^n-1 is a unit through D<=4H even if kn exceeds the literal guard range. Producing D such denominators and inverses still costs soft D. Integers through D are certified units. The dimension-D, band-j system has the displayed unit diagonal and a genuinely j-supported right-hand side. Its formal q-log solution has the correct ratio and normalization, uses only unit-constant formal series, and acquires the whole R at soft D. It is zero safe and correctly reported as slower than the retained whole query.

The short-output matrix Pi has an actual recurrence/known-root description rather than a supplied m-by-D array. The exact gauge inverse has Toeplitz(R), the Q-difference inverse diagonal and Toeplitz(1/(BR)); its long coefficients remain unpaid. For the literal lower-shift operators the displacement ranks are D-1 because their right sides are a unit Toeplitz factor times the rank-(D-1) lower shift. The drafts limit this calculation to those operators and do not assert a general displacement or scalar-query lower bound. The stated primary q-series and ordinary modular-syzygy applicability limits match the source contracts.

The finite adjoint is the exact transpose with zero-extended finite sums. The two-step coefficients cancel their cross term, and four actual degree-j multipoint evaluations acquire all stored arrays at the m required roots. Their endpoint identity is cross-multiplied and valid at zeros; it supplies transport, not amplitude. The negative original indices associated with some B endpoints are explicitly kept auxiliary, with no automatic original consumer. The reverse stencil reaches the two paid coefficient ends only after its trajectory is acquired. Its transpose formula leaves R(t) after subtraction of the known upper tail, so the drafts faithfully identify the unacquired amplitude for that circuit without excluding a different adjoint method.

The upper Newton acquisition is real. Reversing R and the length-D Newton product requires only their first k coefficients; the latter follows from geometric-root power sums with denominators 1-q^(-r), r<k. The U expansion, multiplication by the length-(k-1) product, and degree-(k-1) reversal give an ordinary short Newton conversion with reversed nodes. This acquires the true TOP k Newton coefficients in soft k, while the supplied bottom monomial block remains different from the bottom Newton block. No middle coefficient is hidden in the conversion.

The first actual window relation has the correct indices: denominator F(q^(-r)),0<=r<k, numerator F(q^(-(kG+r))). All2k values are acquired. Denominator nonunits have actual original row/index maps: native roots map to r, reciprocal-image roots map to L0-1-r, both inside the main interval and neither at a tail index. This final source/draft clarification was rechecked at the exact pins above. They are tested/localized before any inverse; the numerator is not inverted. The first Newton pivot F(1)N_k(x_k) is legitimate, with the geometric part a unit. This operation still leaves the k initial amplitudes. Subsequent out-of-horizon coefficients have no unproved consumer: retain cross multiplication or use the zero-safe full solve. The literal all-window and k-by-k matching costs remain explicitly charged; their entry counts are not promoted to a generic lower bound.

The omitted quotient carry is correctly exhibited: P_k(QT) modulo P_k is a unit by the actual short q guards and unit-separated geometric nodes, so it cannot erase u(QT). The claim concerns this raw representative update only. An enriched state or different short contraction remains open.

Old reciprocal/Dickson, canonical-row and coefficient-action work is credited. Every completed product is returned to original rows, main/reciprocal blocks and the two-factor tail before the norm/beta consumer. No auxiliary pivot, arbitrary endpoint or global-zero multiplier is silently treated as a covered original collision. Both drafts retain soft(J+sqrt(JL))=soft k^(3/2), and claim no faster whole query, factoring exponent or completed executable/Lean bit-cost theorem.

Read-only preservation checks: both shared-document baseline prefixes match continuation-baseline.json, and all116 entries currently in source-pins.json match their actual bytes. This audit did not run the append-capable validator or independently recheck all270 inherited manifest members; those and the eventual exact append remain the parent's validator step. No preservation claim beyond the executed checks is inferred from the draft text.
