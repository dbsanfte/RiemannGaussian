# Independent final exact review: unbalanced short-annihilator extractor

Verdict: PASS. One uniformity wording correction was requested and is present in the final bytes. No remaining mathematical correction requested. Read-only classical proof review, not a Lean/build certification.

Final targets:
- `unbalanced-extractor.md`: 9993 bytes; SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.
- `source-pins.json`: 1749 bytes; SHA256 `7c6cd53d7348a12ea34ea48eb539dfa7199292d5429e0b1513a853e3f2895553`.

All three durable prerequisite pins and both inspected Lau--Wu PDF/text fingerprints match exact bytes. The analytic theorem remains an identified inherited primary input; the new argument is its dyadic unbalanced composition with the previously proved separator.

Sections 1-2: a powered trial base has local orders dividing the respective indices because each odd gamma order divides K_0. No coprimality with the index is needed. The universal separator needs only ONE local order below its cap to guarantee a hit. A saturated earliest leaf still proves exact equality of BOTH orders, independently of any bound on the other one. NoHit certifies both exceed the tested square horizon. Monic evaluation, repetitions and gcd localization are correctly inherited.

Sections 3-5: the first Jacobi scan is global and cheap; b_0 is powered once. A largest power of two X<=P for the smaller prime satisfies B/2<X<=sqrt N and P<2X, so the correct bin is enumerated. Its index is below 2X/B<=M_X, guaranteeing a hit on EVERY unit trial there. Any exact-common-order output on the Jacobi-minus base establishes the global unequal-2-adic-valuation fact, even if obtained in a wrong bin. Wrong-bin NoHits or later common-order results cannot invalidate the correct bin and are safely skipped/continued.

For the correct bin both primes are at most Y_X=ceil(N/X), and Y_X>=sqrt N. The uniform least-nonresidue bound therefore places the required nonresidue in the public rounded scan for all sufficiently large N, including when that prime is small. At this base unequal local 2-parts are preserved by odd powering; common-order and NoHit outcomes are both impossible in the correct bin, so a proper factor is returned. No hidden prime, order, local character or balance bound is an algorithm input.

Section 6: M_X=Theta(X/B) for enumerated X, and Y_X=Theta(N/X); ceiling cutoffs and integer-root computation cause no endpoint loss. Per-bin cost is soft N^(5/32)X^(11/32)/m, increasing in X and maximized at sqrt N. With m=Theta(N^(1/6)) this is N^(31/192). Initial scans, per-bin preliminary separators, powers and O(log N) bins fit that bound. The final wording now correctly distinguishes uniform character bounds from SUCCESS IN THE CORRECT BIN; it does not claim every wrong bin must succeed.

Finite-input totality is valid: uniform eventual success limits trial-division fallback to finitely many promised N, and the fixed polylog-bit K contract gives finitely many promised input strings there. K=0 explicitly falls back rather than attempting to strip its nonexistent odd part. Outside the promises no fast bound is claimed. This is an asymptotic algorithm with no asserted numerical Burgess threshold.

Novelty scope: targeted journal searches for Burgess,31/192,5/32,5/64 and dyadic order/annihilator formulations matched the latest BALANCED predecessor only; older dyadic Hasse/carrier and recursive kernel-routing results are different interfaces. The separator and character theorem are inherited, not new. This audit is not an exhaustive priority claim. The substantive extension is the paid conditional extractor without balance or both-small-index assumptions. Acquisition of K, the original query, and full Lean/controller composition remain open.
