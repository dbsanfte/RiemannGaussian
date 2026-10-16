# Independent cyclic reciprocity and exact-phase review

2026-10-15. Reviewed `/tmp/semiprime-input-dependent-20261015/reciprocity/cyclic-reciprocity-audit.md`, SHA-256 `48fb0580a1c90631215c7481ba8833637758ff15cf8c1d8f245cc3f6e067b3c1`.

Verdict: **PASS for all exact algebraic claims and the scoped cyclic-primitive obstruction.** No generic scalar lower bound or exclusion of regularized/noncyclic functions follows.

## Exact identities

* Writing E=d h+r, each original residual gamma^E-q^i equals the known unit q^h times gamma^r-q^(i-h). Multiplying L factors gives precisely the phase q^(hL) and interval start s-h in equation (1). This holds for signed starts and h without inverting a residual. h=Theta(N/m²)=Theta(m⁴) on the actual large scale, so the transformed start cannot be treated as a nearby endpoint.
* Reversal equation (2) follows by factoring -zq^i from each factor and replacing i by L-1-i. It only inverts known units z,q, and preserves length and factor multiplicities. With z=gamma^(-E), its new parameter is gamma^(E-d(L-1)), corresponding to target exponent d(L-1)-E, as stated.
* Distribution equation (3) is a genuine division-free identity: the exponents r+d i cover every integer in [0,dL) exactly once. Sparse source tags cannot be silently replaced by the complete d-sector product. The report correctly confines its cost objection to explicit completion.
* For j=1, a=N mod m and D=(N-a)/m; b=-D mod m. Thus E=N+a+m b-2a=N-a+m b=m(D+b) is divisible by m². The resulting public global zero lies at i=E/m²=Theta(m⁴), outside the native Theta(m²) interval. The interval shift in (1) moves with it and does not create a free valid witness.

## Actual cyclic monodromy

In either retained hidden field gamma has exact prime order R>16m². Since gcd(R,m²)=1, q=gamma^(m²) generates the same subgroup. Every z=gamma^(-E) belongs to that subgroup and satisfies z^R=1. The complete product over one q orbit is exactly 1-z^R=0. This is a full-orbit statement; it does not assert that each row's shorter queried prefix vanishes.

A nowhere-zero cyclic function satisfying W(qz)=c(1-z)W(z), c nonzero, would yield 1=c^R(1-z^R)=0 after multiplying recurrence ratios over the orbit. No such function exists, even over an extension field. The same argument directly applies to any orbit containing the factor z=1. For off-orbit z, the necessary normalization c^R(1-z^R)=1 is correct; invertibility and a root are genuine prerequisites. The actual zero value cannot be repaired by granting root extraction or the hidden order.

Public q-power shifts, Euclidean phase normalization and reciprocal reversal keep targets in the same subgroup. Therefore this obstruction applies to the actual full-N source points and does not depend on a fixed-index catalog. It only excludes a globally invertible cyclic primitive with this recurrence. Noncyclic path accumulation, singular regularization with an independently paid localization theorem, or different scalar algorithms remain open as the report states.

## Primary premises independently inspected

Recomputed every entry of the saved `reciprocity/primary-manifest.json`: all three PDF hashes match.

* Ishibashi PDF SHA `99233c0bf151cc1953cc0ddf8489976d728a66220659fbce132b3e8ccb2ddd43`. Checked publication header (9 July 2026), section 2's known odd order and primitive root, Lemma 2.1, punctured Fermat curve, Definition 2.3 fractional powers/branch domain, and Theorem 2.9 inversion relation. These support the reported nonsingular complete-orbit normalization context. The paper does not supply a finite-composite-ring acquisition clock in those cited statements. The source-specific zero-orbit obstruction here is independently proved algebraically rather than attributed as that paper's theorem.
* Kopp PDF SHA `17764426499b81d2771221fa933a91adb6ae35914755ef9d9d97d5435a8766a9`. Checked v3 date (3 May 2025), abstract and introduction: complex meromorphic modular cocycles and real quadratic special values. These premises do not themselves provide a finite-ring specialization or a collision-preserving bit-complexity algorithm. This review does not claim an exhaustive impossibility result from the paper.
* Radchenko–Wheeler PDF SHA `aae135b3cb875ab24d64e0042cb10ced98b64171dd8a760a4c2a96fe88ba7e71`. Checked v2 date (29 September 2026), abstract and main-results scope: algebraicity of special values and finite quantum-dilogarithm polynomial systems. An algebraic defining system alone does not specify an efficient unknown-order composite-ring evaluator or select the desired root.

The Ardehali–Rosengren analytic-product paragraph is separately attributed to its primary publisher page. At this review stage its PDF is not among the three local primary artifacts; that paragraph's full-text verification is not included in the independent local-PDF checks above. None of the exact obstruction proofs depends on it.

No blocking algebraic error found. Claimed scope and unresolved positive possibilities are appropriately explicit.
