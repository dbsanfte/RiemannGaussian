# Independent targeted locator and forcing review

Verdict: PASS within the stated narrow applicability and failed-attempt scopes. Neither report proves nearlinear acquisition or an actual-source complexity lower bound. No report mutation is requested.

## Exact reviewed targets and hash closure

- locator/report.md: 9067 bytes, SHA256 a72bb78d44efd4a638f33e6730cb457639db3e93e819e66693ec865628c119bf.
- locator/manifest.json: SHA256 fdc378be2079a6dc495a5e61099d8e8b9815a5edecc0d1ca2cad3fc39bf6f0c5.
- forcing/attempt.md: 4720 bytes, SHA256 1199ecd4b40fd9cd22194cf116dcdfe5d9d05e79107d8b333a2b7bd2e68806f2.
- forcing/sources.json: 692 bytes, SHA256 9d2a93b062b1bd87f63781ad32976ab9d22cdbd5dc35ee82df9bfb0db488164c.

Independently verified every one of the locator manifest's 13 file byte counts/hashes and both inherited source pins; all three forcing source pins also match. The five saved PDFs have PDF headers. Regenerating their text with pdftotext -layout gives exact equality to each corresponding saved text. The ECCC saved text explicitly contains the revision notice also present in the saved HTML. This is targeted inspection of primary theorem/model passages, not a complete correctness audit of every paper.

## Primary input/output and cost checks

Kaltofen 1987: introduction, theorem 4, and the preceding uniformity discussion independently inspected in the PDF-derived text. Theorem 4 assumes a division-free input program and a sufficiently large field and asserts output program length O(ell M(h^3)+h^2 M(h^2)). The introduction explicitly says polynomial-time constructibility is lost for the output-degree-sensitive results because scalars derived from the input are needed; the proof discussion likewise says the method does not give an unconditional uniform polynomial-time construction from the input program alone. Thus the report correctly separates output circuit existence from a nearlinear uniform constructor. Its rejection does not rely on confusing circuit size with dense output size. The exact large-field condition remains an explicit premise in the primary statement; the report does not claim an unconditional small-field theorem.

Kaltofen 1988: independently inspected abstract and model/algorithm discussion. The input-degree bounds are unary parameters and the transformations have controllably bounded-error randomized polynomial running time for the usual coefficient fields. This is a genuine uniform result but supplies neither a soft O(s+d) nor soft O(s+h) constructor. The report does not replace this polynomial bound by a nearlinear one or assume field divisions over an unfactored composite ring.

Directed Evaluation: independently inspected theorem 4.2 and its detailed cost specification. It requires an explicitly separable K[x]/mu and gives exactly the displayed detailed-cost bound with multiplicative algebra dimension. Output channels also incur the tau_out M(d) term. The small degree of a factor not yet acquired does not replace the input algebra degree. This supports the report's applicability limitation, not a lower bound against a more structured implementation.

Constant-depth GCD 2025: independently inspected theorem 1.1 and its immediately following algorithmic interpretation. The field must have at least n^c elements; the ratio circuits have polynomial size and constant depth, piecewise with tests. The parallel input consists of the two coefficient vectors and the work involves polynomially many processors. This does not assert nearlinear total work on an unevaluated vector SLP.

ECCC TR25-171: independently inspected the saved primary revision page/text. Revision 1 is dated 28 January 2026. Its changes notice explicitly reports a gap in the proofs of theorems 6.2 and 6.4 and states that all results crucially depend on them. The advertised model is coefficient-vector input, infinite fields, divisions, and border computation. The report correctly imports no claimed nearlinear bound from the paper as an established exact extractor.

Single-seed Hensel 2026: independently inspected title, abstract and input/seed discussion. The setting is X^n-1 over a supplied prime-power ring, n coprime to the supplied prime, with a seed factor over its residue field and cached inverse/coset data. These prerequisites do not instantiate a common-factor extractor over an unfactored squarefree semiprime. This review does not validate the preprint's performance, benchmark, or all internal correctness claims; those are unnecessary for the report's input mismatch.

## Mathematical checks

The Wronskian identity follows by the product rule: for N_r=H A_r, derivative cross terms in H H' cancel and the result is H^2(A_r' A_s-A_r A_s'). It holds over arbitrary characteristics. Ratios cancel H as rational identities; logarithmic derivatives retain both H'/H and cofactor contributions. These identities do not alone acquire a gcd or separate those contributions. The report correctly limits the conclusion to that proposed normalization and permits extra source information or different differential algorithms.

For the forcing note, F(alpha qx)/F(alpha x)=(1-qx)/(1-alpha x), alpha=q^(1-L). Hence U A(qx)=V A with U=(1-alpha x)Dhat(qx), V=(1-qx)Dhat(x). Coefficient extraction gives the displayed forward pivot q^n-1. Since U_(J+1)=-alpha q^J d_J and V_(J+1)=-q d_J, the trailing pivot is d_J q(1-q^(n-L-1)). Both pivots are units for 1<=n<=L under the inherited order/unit-power assumptions. A zero window of J+1 coefficients in that prefix propagates backwards to contradict a_0=1. This is fieldwise, not a claim every nonzero coefficient is a composite-ring unit.

P=K(x^B)A introduces exactly the displayed convolution. The no-zero-run assertion for A is not proved for P; cancellation is explicitly left uncontrolled. Eliminating A multiplies by K(x^B) and K(q^B x^B), yielding degree JB+J+1 multipliers as stated. Direct coefficient propagation costs O(JM) operations and O(J) state; its cubic balanced-regime clock is not presented as an improvement. No degree-to-operation lower bound or Omega(JB) pole claim is inferred.

The paid boundary inverse only interconverts supplied rows and forcing. Neither note assumes the missing tail or its constants have been acquired. All conclusion scopes and accounting qualifications are appropriate. No repository edit, build or new research search was performed for this review.
