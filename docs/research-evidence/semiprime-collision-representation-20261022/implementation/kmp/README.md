# Gcd-aware KMP: exact explicit-vector orbit matching

`gcd_kmp.py` is a standalone Python reference. Run `python3 -m unittest -v test_gcd_kmp.py` in this directory. No dependencies, hidden factors, randomness, sparse-discrepancy promise, or native long-query evaluation are used.

## Theorem and proof

Let N>=2 be squarefree. Replace EVERY symbol equality in both KMP prefix construction and text matching by g=gcd(a−b,N). Return a proper factor when 1<g<N; return true when g=N and false when g=1. If no factor is returned, every reached comparison has the same answer in EVERY field F_p for p|N: g=N means equality in all fields, and g=1 means inequality in all fields. Induct on comparison steps, including prefix-function construction: the arrays of prefix lengths, machine state, next comparison indices, and reported positions coincide with ordinary KMP run modulo each p. Consequently the returned position list is simultaneously the EXACT full occurrence list in every hidden field. If any two local occurrence sets differ, a proper factor MUST have been returned. The converse is not claimed: prefix construction may reveal a factor even when final occurrence sets agree.

This also proves that hidden-field disagreement in a late coordinate, or two local matches at different shifts, is covered. Comparing only a predetermined coordinate or fingerprint would not suffice; the adaptive KMP transcript does suffice because every comparison is screened.

The ordinary KMP bound applies unchanged until early termination. Prefix construction uses at most 2d comparisons and matching at most 2n, so at most 2(d+n) gcd calls. With pattern B of length d and text A+A[:-1] of length 2d−1 this is <=6d. Results have O(d) positions. Empty general patterns match every text boundary; the cyclic empty/empty case has the sole canonical offset 0. Unequal cyclic lengths and invalid integer inputs are rejected. A factor result discards partial occurrence lists.

Each comparison operates on O(log N)-bit canonical residues. Thus total bit work is soft O((d+n)log N), including input/output bit size and fast gcd; Python uses its built-in arbitrary-integer gcd. This is linear in the explicit vector length up to arithmetic logarithms. It is not linear in the size of an implicit matrix whose rows have not been acquired.

## Automorphism wrapper

For an odd public prime m and a supplied public primitive root g of F_m, index nonzero coefficient positions by g^k, 0<=k<m−1. The wrapper checks primality and primitivity using trial division/factorization within soft O(m) metadata work; finding the root is not part of this API. It first screens coefficient zero with the same gcd comparator. A unit difference there implies there are no whole-vector matches in ANY hidden field; a proper gcd returns a factor.

For the remaining coefficients, put a_k=A_[g^k], b_k=B_[g^k]. Since rho_j sends X to X^j, the coefficient of rho_(g^s)(A) at g^k is a_(k−s). A cyclic occurrence b_k=a_(k+r) therefore corresponds to j=g^(−r), not g^r. `automorphism_matches` returns these j values in `Result.positions`, with at most 6(m−1)+1 gcd comparisons. The fixed A,B must already be explicit; this does not acquire the native tag/index-dependent source vectors.

## Tests and scope

Five test groups compare against independent naive local occurrence oracles: exhaustive residue-alphabet arrays through length three, mismatches confined to a late coordinate, differing full local shift matches, equal/repeated arrays, long KMP failure chains, prefix-table factor discovery, signed representatives, empty/invalid inputs, and coefficient-automorphism matching with independent inverse-index permutation. Comparison counts are checked. These are algebra/control tests, not empirical evidence for factoring-family coverage.

Primary KMP source: Knuth, Morris, Pratt, *Fast Pattern Matching in Strings*, SIAM J. Comput.6(2),323–350 (1977), https://www.cs.jhu.edu/~misha/Spring23/Knuth77.pdf. The modification is justified by the transcript proof above; it requires no new string-matching theorem.
