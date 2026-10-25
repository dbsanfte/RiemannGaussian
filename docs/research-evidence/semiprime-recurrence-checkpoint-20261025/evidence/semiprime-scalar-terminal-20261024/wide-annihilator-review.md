# Independent review: explicit short-atom wide annihilator

24 October 2026. **PASS.** Exact source wide-annihilator-lemma.md SHA256 `6fa449a65eb7e94ea82750a34c4fd63f8fe2cd9e7b3bb47f40bd53efc9d4a7f6` was read. No correction required.

The coprime-base step and total-width accounting are valid. Every used generator divides the atom product, each generator divides an input atom, and their total logarithmic size is at most the input width. Removing signs, ones and duplicate support causes no problem: the later exponent cap replaces valuations, not the annihilator's prime support. Under the large-order promise there cannot be no nontrivial generators.

With e=ceil(log2N), each local beta order divides product(g_j^e), since all its prime support occurs among the atoms and each valuation is at most e. Each composite leaf A_j has O(log²N) bits, and their TOTAL width is soft L. The complementary-power invariant is exact; sibling exponents at each depth have total bitlength O(T), so the full tree costs soft T modular work, not T independently for every leaf.

If every complementary projection were1 globally, beta's order would divide gcd_j(K'/A_j)=1, including the single-leaf case. Otherwise, absent a proper gcd, at least one projection has a unit difference. Its two local orders remain odd, nontrivial and coprime. The ONE exact-common-order screen therefore either factors or certifies both orders>16H: a common small order would have to be1, contradicting selection. No screen is needed for each leaf. The selected A_j is a positive polylog-bit global annihilator, so the pinned unbalanced extractor's stated fixed-polylog input-length and order promises are met. Total soft(k+L) is correct.

The cited extractor was checked at its explicit polylog-bit K interface. Bernstein's cached primary Algorithm18.1/Theorem18.2 and its M-time definition support input-width times polynomial logarithms with fast integer arithmetic; this is not an uncharged n^(o(1)) assumption.

The current implicit AP-product does NOT supply a soft-k explicit atom list; the source clearly preserves that missing acquisition. A product of beta^d-1 is not beta raised to the product of d. This is a reusable conditional consumer, not a query advance. Only this review was written; source/shared files were unchanged. No further research or validation is claimed.
