# Independent review A: uniform recurrence barrier and chirped degree

2026-10-16. Read-only mathematical and source-fingerprint review. Verdict: PASS for the exact targets below; no acquisition or general complexity lower bound follows.

## Exact targets

- `uniform-recurrence-barrier.md`: 7000 bytes, SHA256 `22d22246cce49eb933e831a93651aa467bfdcf2f8a6c38f974b47dbecc9eda8a`.
- `chirped-stream-degree.md`: 3677 bytes, SHA256 `61d007c9cef02d35e3da5860c7c00f99ce577c19cea5ac62b894bac0e65f40f9`.

## Uniform arithmetic and clock

The paid setup supplies beta with odd coprime local orders above 16m² and global order above 256m⁴, and separately certifies both local orders of q=beta^(m²) above 16m². These premises suffice without prime local orders or an assumption that m is coprime to either order. Their balance/scale hypotheses are inherited explicitly.

The degree-2m monic product over beta^t, t in [-m,m] excluding zero, can be evaluated at the m points q^s by monic subproduct/remainder trees over Z/N. Point-difference inversion is unnecessary. A unit product certifies every factor unit. A saturated row can be localized by gcds along its retained product tree; a proper gcd is a factor. Reaching a saturated leaf would imply a global annihilator K=m²s-t, with 0<K<=m³+m<ord_N(beta), a contradiction. Thus the algorithm returns a proper factor or certifies the complete signed square-alias catalog. Ordinary fast polynomial arithmetic, successive powers, m gcds and at most one localization path cost soft O(m log N) bits. The certificate is implicit in row products; the algorithm does not output m² individual residues.

The higher-order ratio and its sign are correct: the c-coefficient ratio is -(q^k-q^L)/(1-q^(k+1)), and chirping contributes beta^(-tk-binom(t,2)). Clearing denominators produces exactly the displayed B_t, of degree <=D+r and nonzero iff P_t is nonzero. All cleared denominators on required k are units fieldwise because k+r<=L<ord(q). All A_k are nonzero for the same reason.

For two frequency pairs, a collision is beta^(d s-v)=1. Axis cases are excluded by local beta/q order bounds. Mixed cases reduce, by reversing both signs, to 1<=s<=m and 0<|v|<=m, precisely the paid alias certificate. Thus the frequency bases are distinct in each hidden field. Under r+D<=m, their number is at most (m+1)². There are L-r+1>=2m²+3-m>=(m+1)² equations for m>=3. Field Vandermonde invertibility forces every B_t, hence every P_t, to vanish. This holds for fully input-advised field coefficients.

## Chirped g-stream degree

The displayed rational ratio has denominator degree d+1 and is regular on all L nodes. Any alleged degree-at-most-d representation gives a cross polynomial of degree <=2d+1<L with L distinct roots, hence the zero polynomial. Its displayed numerator and denominator are coprime because q^(L+1)!=1 and the numerator is nonzero at zero. Consequently the degree-(d+1) denominator divides the alleged denominator, a contradiction. No separability assumption on X^d is required. The minimum max-degree is exactly d+1. The Bluestein identity and its geometric rescaling qualification are correct.

## Sources and algorithmic interpretation

Independently checked all six hashes/byte lengths in `/tmp/semiprime-wide-annihilator-20261016/coprime-source-pins.json`: the paid preprocessing, extractor, separator and three native files. The inherited coprime-refinement report is 9447 bytes, SHA256 `d4477d8a27050922f50354ca89f075b9d246adfc608eb9b486f01be4b4a74c76`.

The existing durable Bostan–Yurkevich source is `docs/research-evidence/semiprime-long-query-20261015/primary/qproducts-by.pdf.gz`: 370577 bytes, SHA256 `fb407530f83eb83df60633879c29f005d58a774efd9eab089cfe1461e70220be`; decompression independently checked to 499386 bytes, SHA256 `f3d617af2e9c899b41d5f4d9120412c78857ebc19009b69fe99e74d97f0d9b09`. Primary URL: https://arxiv.org/pdf/2012.08656v1 . Existing extracted text: `/tmp/semiprime-direct-frontier-20261016/norm/qholonomic.txt`, 121716 bytes, SHA256 `ae779c48d317414bc0223e381d6bc40296c5c9630903b4959e715e6b14d63c83`.

Theorem 5, printed page 16 with degree accounting on page 15, gives O(r^theta sqrt(Nd)+r² M(sqrt(Nd))) field operations, with coefficient degree d>=1, N>d, and Theorem 3's nonzero leading-coefficient evaluations. This is an upper bound with growing parameters charged, not an operation lower bound and not automatically a composite-ring algorithm. The new proofs are self-contained and do not depend on this primary result.

The older generic recurrence obstruction §G15 concerns U_n=product_i F(theta^i), with target-pole uniqueness. The present A_k is a different chirped q-binomial coefficient stream. Prior recurrence techniques and the classical detector/evaluation mechanisms should be credited; no claim of the first recurrence obstruction is justified.

## Limits

The uniform branch proves a format-specific r+D>m condition in both fields, after soft-m preprocessing that may instead factor. It neither acquires the original norm nor transfers the original literal base-2 collision coverage to beta. It does not exclude order 2m, O(m polylog m) recurrences, another geometric base, multivariate coefficients, implicit selected convolution, or a nonlinear scalar norm method. No upper bound was used as a lower bound, no generic operation lower bound was proved, and no new native/Lean result was checked or asserted. No repository files were changed and no builds were run.
