# Independent exact-source literature review

24 October 2026. **PASS.** Final source literature.md SHA256 `6cd4ab03933c048f1490f5af2f8cb590a9740188e94188d518f00a0fe5516d68` was read independently. One minor input-size clarification was requested and verified: J<=2 is handled directly; the literal three-column generator is supplied to Algorithm3 only for J>=3, satisfying alpha<=J. No remaining correction is required.

Primary caches read and verified:

- Khichane–Neiger2026 PDF: `6f8256f25eeb11c1dc3b67e8f91bd1c58b8c3f40f2261c5c268738fb7e51b4bf`, especially pp2–3, Section3.1, Theorem1, Theorem25 and Algorithm3.
- ECCC TR25-171 original PDF: `6bc58fb6ea165c5704396d52675f35cd601cda11a792dfc23c2d01b0f85b7139`.
- Primary ECCC revision/status page: `8d528c7c854902770154a27214d9a5855b6ac6053225a4701ccf0ae3ec596ae1`.

The Stein formula is exact with the stated Bezout sign convention. Setting D0=KR gives SD0-D0S=(fh^t-hf^t)R. Multiplication by S^t and SS^t=I-e0e0^t gives D0-SD0S^t=h(e0+SRf)^t-f(SRh)^t. The added e0 e_last^t has that same Stein displacement. This proves the displayed rank-at-most-three generator over the actual commutative algebra, without target inverses. Its first column equals h because S^t e0=0 and D e0=h for J>=2. Any explicit alpha-column generator therefore recovers h by a length-J matrix-vector contraction costing O(alpha J). This is a limitation of this particular input interface, not a general representation lower bound.

The unit regularization and reversal solve have the claimed local kernel. At a simple unique common root V the evaluation vector is killed by K and has first coordinate1, so the regularized matrix sends it to e0. Tag interpolation recovers the old weak label. This does not acquire h. Supplied h already permits the old guarded polynomial-gcd recovery, so no query advance is counted.

The primary deterministic solve theorem uses effective fields, supplied generators and RHS, with the stated alpha-dependent bound. Its Toeplitz-like operator is exactly the nilpotent Stein operator used here; no unsupported cyclic extension is imported. The absence of generic-rank or random-preconditioner assumptions is accurate. Vandermonde/Cauchy distinctness and disjointness hypotheses remain explicit. The source's separate guarded composite adaptation is valid: a norm-unit element is invertible; a proper norm gcd factors; norm zero at the nonsplit field forces both coordinates zero there, so coordinate gcds either factor or certify global zero. On a no-factor trace every zero/unit branch agrees in all simple components. This costs logarithmic-bit gcd work per field operation/test and does not provide the missing generators.

The primary ECCC status page explicitly dates revision1 to28January2026 and reports a gap in Theorems6.2 and6.4, on which all results rely. The report correctly declines to use the apparent border-composition/GCD claims as established. Exact composite-ring execution is separately distinguished from border circuits with explicit coefficient input.

The final source makes no faster whole query, factoring exponent, or generic impossibility claim. Its old soft(J+sqrt(JL)) acquisition remains paid. Only this review was written; the author repaired its own source. No shared documents or frozen primary files were changed and no preservation validator was run.
