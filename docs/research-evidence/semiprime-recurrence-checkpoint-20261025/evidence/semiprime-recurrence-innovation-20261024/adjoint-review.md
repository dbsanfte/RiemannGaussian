# Independent adjoint audit

Date: 2026-10-24. Reviewed source: `/tmp/semiprime-recurrence-innovation-20261024/adjoint-attempt.md`.
SHA256: `5ba2d08b5ba4ceeb4f06c410b092e2a2b4606e4e4800b95c1c76ca8c1376f842`.

Verdict: pass as a negative audit of the specified algorithms. No sixth-rate algorithm or general lower bound is established.

The companion-inverse conversion is correct: each q^i-Y_j equals -Y_j(1-q^i/Y_j), giving precisely the displayed sign and unit scalar. The trace expansion follows by expanding each (1-t q^i Y_j)^-1 formally at t=0. This is legal over Z/N because the constant term is one. The reversed polynomial has constant term one and its logarithmic derivative supplies the short power sums without integer division. The geometric quotient has the stated guarded denominators; binary doubling provides a division-free alternative at soft(J log h) work. The word soft hides that logarithm legitimately. Unit-separated nonzero roots imply J≤p-1 for each prime p|N, so integer divisions through J in the short exponential are lawful.

The initial scalar jet provides no terminal value. In characteristic zero with independent root parameters and generic q, the Jh poles are distinct; at t=1/(q^iY_j), the logarithmic derivative has residue +1. Consequently its reduced denominator has degree Jh. This refutes a universal degree-O(J) Padé reconstruction under the displayed hypotheses. It does not prove impossibility on every finite-field native instance, and the source appropriately refrains from such a claim.

The exterior-power identity is exactly multiplicativity of determinant and retains the degree-J multiplier. Its soft(Js+h/s+J) block ledger is correct in the relevant h≥J regime. The Schur bilinear action also has correct indices: the coefficient at h+J-1 receives a_(h+r-c) from z^(J-1-r)z^c. Thus ordinary short convolution does not acquire this far coefficient. A fast determinant-only algorithm remains logically possible, as stated.

Minor clarification only: the generic-pole calculation concerns the reduced denominator of E'/E, not the polynomial degree needed by every conceivable scalar algorithm. No change needed because the source already makes that distinction. No source mutation performed.
