# Independent review: actual uniform shift boundary

2026-10-16. PASS, with no requested correction. Read the full final report; independently derived the arithmetic before reading its proof.

Reviewed report: `/tmp/semiprime-forcing-query-20261016/forcing/uniform-shift-boundary.md`, 8065 bytes, SHA256 `9b82f2761f8c74b8e0412718805c2b7d5a209ed138cd53aa9596ba7a11c6de93`.
Reviewed source manifest: adjacent `uniform-shift-source-pins.json`, 1127 bytes, SHA256 `246a89c38bbb6701659ae52c976a1729b4e69640917431f4b845c6ae0ac7f943`.
All four listed source files were rehashed and their byte counts checked: every pin matches. The native offset congruence/band and inherited fiber, weighted-descent and unit-row-density premises support the stated contract. No new native theorem or analytic deletion is claimed.

The complete square image is correct: t ranges over nonzero residues, u=t-1 omits only -1, and u=+1 preserves its square. Thus the image includes zero and is exactly N(S-1), not a punctured square set. Its cardinality is (m+1)/2; deduplication retains every low class, and each class has at most two nodes.

The exact character formula is correct including its zero contributions. The factor-pair count gives sum chi(x)chi(x-h)=-1, and expansion gives intersection (m+1+chi(h)+chi(-h))/4. Therefore the stated boundary is at least ceil((m-1)/4). All divisions in this argument are in the odd-prime field F_m, where N is invertible.

The multiplicative-to-integer reduction is valid: all offset differences lie in [-4d,4d], and R>8d makes a representative unique. If none exists there are no edges. A nonzero displacement divisible by m yields disjoint single edges inside fibers of size at most two. Otherwise every low class in A minus (A+c) supplies a dangling node, with the direction a-c checked explicitly. These cases exhaust every fieldwise nonidentity scalar, including privately advised choices and shifts outside the gamma subgroup. No menu or union bound is needed.

The weighted-descent divisibility test, numerator-degree consequence and H^s multiplicity extension follow by evaluating at simple roots. The universal representative-change map has exactly the stated rank because evaluation at the distinct shifted nodes is invertible. Subtracting o(m) inherited zero rows leaves the claimed linear number of lost nonzero rows or defect coordinates.

The fieldwise qualification is essential and is explicitly present: nonidentity modulo N need not be nonidentity in each component. The gcd(rho-1,N) split handles that distinction without supplying private orders or discrete logarithms. Algebraic rank is not asserted to lower-bound arithmetic operations. The report correctly leaves fixed-payload syzygies, pole gauges, boundary corrections, finite-grid algorithms and moving carriers open. This is a substantive uniform actual-source carrier obstruction, not a whole-query impossibility result or improved acquisition algorithm.

No source or report was edited; no build, experiment or broad literature search was used for this review.

## Final extension review

The final report is 9832 bytes, SHA256 `028d106682957fe8f12c39b4045b9b0347851648b08bc8bd6380db22d24ce0ed`; final source manifest is 1337 bytes, SHA256 `209c45721ac48425029afe13d65a05229f0f62df022d436dfce7eed9e72dd545`. All five final source pins match. The earlier reviewed text is unchanged; §7 adds the exact powered-node compatibility defect, which was independently checked.

The Lagrange entry identity remains valid at overlapping nodes without dividing by their difference. The factorization has a full-row-rank b-by-J right Vandermonde, so multiplication by it preserves the rank of the left factor. The surviving left rows form a Vandermonde at distinct shifted nodes; its rank is exactly min(b, dangling count). Hence the exact rank formula, balanced dyadic b consequence and uniform linear rank are correct. The stated limitation excludes only a small explicit powered-node compatibility generator and explicitly does not infer ordinary mixed-commutator rank, arithmetic cost, or failure of a different generator. Final verdict remains PASS.
