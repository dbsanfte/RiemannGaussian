# Independent exact-source cubic-cover review

24 October 2026. **PASS**, no required corrections.

Reviewed cubic-cover.md SHA256:
`9ca92557ef8b5229143e0ac2162e890d87b3b61d8bed18ce4bb1d0fd6844dec2`.
Also read the actual inherited general extractor; its bytes match the stated SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`. Reviewer changed no source/shared files.

The triangular integer basis has determinant exactly k³ and parameterizes both congruences, without a hidden primeness assumption on k. Defining ell0 as stated makes f(j) vanish modulo k³ and f'(j) vanish modulo k²; the coefficient 3aj+b vanishes modulo k. The exact cubic Taylor expansion then gives f(j+kx)=0 modulo k³. Since the actual own P is coprime to k, division by P yields the integer index in (3). Nonzero lattice vectors with a=0 remain valid.

The rational derivative-coordinate map has absolute determinant N Delta^6/P0^4. Common-denominator clearing and rescaling preserve its exact lattice and the fixed-rank LLL first-vector bound sqrt(2)*det^(1/3). The map is invertible, so the acquired triple is nonzero. Formula (7) is the exact rational Taylor identity; its three terms are bounded by T,T,2T respectively, giving 4T. The displayed coefficient bounds imply polynomial magnitude, hence O(log N) bit length at the actual public cutoffs.

Exact floor(Z+1/2) handles signed centres correctly. The signed window has width 2U+1 and is shifted to ordinary nonnegative indices with the SAME q_c and U in a bin. Difference (10) has the correct sign and coefficients. The quadratic J(P)=0 is equivalent to a zero own exponent (P>1), and J is nonzero whenever the triple is nonzero. The integer-root pretest precedes removal of any public zero-position row. Since q_c preserves the actual beta orders by k-roughness, h<16H excludes a second local index in that row. Removing the whole row therefore cannot discard the own witness on a continuing input. All retained leaf exponents K are explicitly nonzero.

The general annihilator extractor really accepts such nonzero polylog-bit GLOBAL K with odd local beta orders>16H, without balance, coprime local orders or a factorization of K. A saturated scalar leaf supplies exactly this promise. The report does not substitute the bounded factor-sum decoder. Row saturation is localized to an actual scalar leaf; different hits at P,Q cause no gap.

The explicit public bins cover the smaller prime. Their centres can remain >=S and comparable to S, with radius Delta and Delta<=P0/2, so the single common T bounds all rows. Substitution of Delta_star gives J_S and h both O(N^(1/9)S^(2/9)), uniformly <=O(N^(2/9)). The cap, Delta>=1, and h<16H checks fail only on a finite input range under fixed sixth-root constants, so the stated total deterministic fallback preserves the asymptotic bound. Each centre/tag lattice, signed exponent, quadratic root pretest and row is actually acquired. The degree-h clock polynomial and all J_S evaluations cost soft(h+J_S); a single successful saturated row can be localized by h leaf scans within that budget. One general extraction call costs soft k. Thus the complete stated promised-branch algorithm, rather than only its cover, has soft N^(2/9) cost.

The contribution is an alternative changed scalar family with more rows and a shorter clock than the previous native query. It neither solves the old fixed-input endpoint in soft k nor improves the separate known one-fifth algorithm. The source states those distinctions and does not claim an overall factoring record, complete Lean bit proof or a sixth-rate solution. No unsupported multivariate-root independence, nonzero cubic coefficient or unit collision output is assumed.
