# Independent two-stream audit review

2026-10-15. PASS; no mathematical or scope correction requested. Read-only review, no original-report mutation.

Exact targets:

- `/tmp/semiprime-multistream-query-20261015/two_streams/report.md`: 7128 bytes, SHA256 `23592400c1a5693041426f01c6a60b46e32c5006fc91a5f5d4d62342d11a30fe`.
- Adjacent `sources.json`: 795 bytes, SHA256 `92605b0af7bf3f2f2a674b3efd56f67f87db4ac4c3934f255105893b6105e8b4`.

Recomputed all four listed primary PDF/text lengths and hashes; all match. This integrity check does not assert independent full-paper inspection. The original investigator inspected those PDFs; this review freshly opened NIST DLMF 17.6.E2/section17.6 directly and checked its exact first q-Chu--Vandermonde formula. Background Heine/finder-paper summaries remain investigator-attributed.

For DLMF E2, substituting n=L, a=q^(-K), c=zq^(-K) gives argument c q^L/a=zq^L, and the ratio on the right is exactly P_L(z)/P_L(zq^(-K)). Double termination restricts the sum to k<=K. Multiplication by the full normalizer and cancellation of its first k factors leaves P_(L-k)(zq^(k-K)), with precisely the coefficient B_k written in (1). The cleared expression is polynomial in z, with only the explicitly displayed unit (q;q)_K denominator remaining. Therefore its specialization remains legitimate at collision zeros; the original rational display is correctly forbidden there. Its coefficient metadata is cheap, but its long products are explicitly unpaid.

The negative-normalizer statement is correct in odd characteristic and odd q-order: zq^r lies in an odd-order subgroup, so -zq^r cannot be 1. Enforcing c/a=z with c=-z gives a=-1, which cannot equal q^(-K) in that subgroup; thus this particular terminating specialization is unavailable. It is not a no-go for other transformations.

The two-stream construction is exact for ANY scalar list modulo squarefree PQ, as a privately advised representation by arbitrary forward prefix streams. Their values 1,P,Q,PQ=0 represent the four prime-zero supports. In the P-only case write a=P*a' modulo PQ, take u=a' modulo Q and a nonzero residue modulo P by CRT; u is a unit and uP=a. The symmetric construction and unit/zero cases complete the claim. This is not a construction of public q-binomial streams or a factoring algorithm. It correctly shows only that incomparable supports alone cannot prove an impossibility for arbitrary two-prefix-stream encodings.

The q-Lucas formula has the stated necessary primitive-order/characteristic scope; the usual Gaussian sign factors cancel when grouping complete root-of-unity blocks. If gcd(r,N)=1, Phi_r(q)=0 in each hidden field forces the order of q there to equal r. The inherited supply really does impose R_P!=R_Q: inspected the frozen `full-euclid-all-hit-obstruction.md`, SHA256 `fb77b60fcf84ffad92c535bd6a0a3d9cc2434beadf48bbf86a39a2a2c8358bb0`, its E5--E7 passage explicitly removes cross-period pairs and records the resulting distinct exact projected orders. Thus the common-r specialization is unavailable on that supply. No claim is made for characteristics dividing r or for all cyclotomic algorithms.

The final costs and limits are accurately scoped: short coefficient acquisition does not pay the remaining long row values, two advised streams are algebraic counterexamples to an overbroad nesting argument, and no public nearlinear weighted evaluator, factorization exponent improvement or general multi-stream lower bound follows.
