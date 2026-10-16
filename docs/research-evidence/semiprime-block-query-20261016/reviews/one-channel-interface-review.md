# Independent review: one-channel restriction-stable gcd interface

2026-10-15. Verdict: PASS. This is a conditional positive interface, not a fast acquisition algorithm.

## Exact bytes and prerequisites

Reviewed `/tmp/semiprime-decimation-query-20261015/one-channel-query-interface.md`, SHA-256 `35770ef9ef864103ecf6ddea449a18698d3481d1473cea56da348a9548a921a7`.

Independently read the prerequisite decimation report, 10005 bytes, SHA-256 `65a5c827a64b5c035d3d0a7bed445c6970910f9f92749309878d1e1520e5c4fd`. All THREE artifact entries and FOUR inherited-source entries in its manifest were independently byte-length/hash checked and match. No repository file was changed and no build was run.

## Algebra and edge cases

For J>=1 and ell>=1, the chosen dyadic B satisfies ell/B<=J and B>=1. Hence

    (ell+J(B-1))/B = J+ell/B-J/B < 2J,

so deg K<=2J-1. This includes ell=J,B=1 (degree J), J=1 (degree at most one), and ell<J,B=1 (degree ell<J). Empty intervals or empty subsets are separately known empty products. No assertion requires B~ell/J when ell<J.

The polynomial mask exists over R because it is exactly the product over nodes of sum_(h=0)^(B-1)(t/x_j)^h. Cartier projection of F times this mask gives the reviewed transport identity

    K(x_j^B)=F(x_j)E_B(x_j)/B.

Its proof is valid in each odd-characteristic field using a splitting extension containing the dyadic roots of unity; only the surviving phase contributes at x_j. This is an equality of quantities already defined over R, hence descends modulo the squarefree semiprime. No extension construction is an implementation cost assumed away.

Each ratio x_j/x_l lies in the promised odd-order subgroup. For a nontrivial ratio, dyadic powering cannot turn it into one, so its geometric sum is nonzero in each hidden field. For a ratio equal to one the sum is B, also nonzero because the characteristics are odd. Therefore E_B(x_j)/B is a unit. This also explains why repetitions do not invalidate the transport identity; after deduplication, retain positive integer multiplicities for the final product. Those powers preserve prime-zero support even when a multiplicity happens to be divisible by a hidden prime.

Multiplication by the rowwise units preserves the zero set in EACH field. For squarefree N, the gcd of the product is therefore exactly preserved, including gcd 1, a proper factor, and N. Replacing K by any representative modulo D_B preserves all its evaluations, so acquiring the full degree<2J numerator is not necessary. The report does not quietly demand all B Cartier channels, one channel per row, or a derivative value as input to the gcd query.

## Paid postprocessing and restrictions

Given K (or its degree<J remainder), powering the J nodes uses O(J log B) ring operations, monic multipoint evaluation costs soft O(J), multiplication costs O(J), and a final integer gcd costs soft O(log N) bits. Thus for polynomial-size ell the stated soft O(J log N) bit and soft O(J)-residue storage bounds are appropriate. These steps do not divide by node differences, row values, B, or derivative values. Optional recovery of exact row values is a different, correctly stated unit-inversion contract. Metadata construction before acquisition may use the supplied units' inverses and must charge their computation; the report already places construction/inversions inside the missing oracle's contract rather than the inversion-free postprocessing claim.

For a common seed interval [a,a+ell), x_j=z_j q^a gives exactly P_ell(x_j;q). A common unit scaling preserves subgroup membership, equality classes, and unit pairwise differences. Dyadic powering preserves the latter promise because it is injective in both local odd subgroups. Public deduplication of equal integer source offsets is justified on the retained family by offset span<local orders; the common interval scaling does not change duplicates. Rebuilding metadata and the denominator for a subset has the stated soft subset-size cost, including logarithmic exponent work. Independently shifted row origins are expressly outside this restriction replay.

## Meaning of the positive interface

The result identifies ONE small polynomial (or one remainder) sufficient for the exact restricted gcd payload. The nonzero-mask-phase and all-Fourier-branch results do not force acquisition of unrequested outputs. This is a useful sharpening of the algorithmic target; it does not itself acquire its coefficients. Selected coefficients or jets of F alone do not supply coefficients of F E_B. The scalar missing acquisition, all-input promised-branch routing, controller bit/memory proof, and full Lean sixth-rate theorem remain unproved, as the report states.
