# Independent targeted primary-literature audit review

2026-10-16. Verdict: PASS on the corrected final report. This review inspects the identified theorem/model passages, not every page or proof of the four papers, and makes no exhaustive-search claim.

## Exact reviewed bytes and payload checks

Reviewed `/tmp/semiprime-syzygy-query-20261016/literature/report.md`: 8317 bytes; SHA-256 `d061b65e80fb82481b5585e2be126496714aca0fc8acee067ef88d058c2c35b9`.

Adjacent manifest: 1781 bytes; SHA-256 `e9877a7ed543f0436d08c48be34b5b502f0fb756f1f68758ef7685a0aaeb12a0`.

All NINE file entries (four PDF/text pairs plus report) and the frozen prerequisite-bundle entry independently match recorded byte lengths and hashes. Re-extracting each saved PDF with pdftotext -layout produces a byte-identical corresponding saved text, so the passages inspected below are tied to the pinned PDFs. No original or repository file was changed. The earlier report SHA ecb079c4... was reviewed provisionally; its sole requested correction was making the Ahle--Knudsen bound explicitly MONIC. That correction is present in the final bytes above.

## Ahle--Knudsen: exact preprocessing and operation model

Inspected the saved abstract/introduction, section 2 model and rational-section definition, and Theorem 1 with its characteristic remark. The main theorem is for MONIC degree-n polynomials in characteristic zero or p>n. A nonmonic leading coefficient adds one multiplication, as the introduction explicitly states. Fixed field-scalar multiplications are free in the paper's primary model, while products involving x or preprocessing parameters are charged nonscalar multiplications; additions/subtractions have a separate count. Rational preprocessing is a section of the coefficient parameterization, and their main construction is everywhere defined over its stated field class. This is not a procedure acquiring a missing coefficient vector or a uniformly shared compiler for the implicit block matrix.

The report now states the monic condition and correctly treats the Theta(L) charged multiplication scale and unacquired block-coordinate preprocessing as an applicability mismatch, not an acquisition lower bound. Composite denominator validity is a separate unit/factor contract. The official [arXiv abstract](https://arxiv.org/abs/2609.06022) confirms the September 2026 submission and monic bound. No unrelated characteristic-two subcase is imported.

## Couveignes--Lercier: supplied elliptic bases and coordinates

Inspected the saved problem definitions and reduction-coordinate input, section 2 summary, the two-isogeny recursion contract, and Proposition 3. The inputs include an odd-characteristic field, an elliptic curve, a rational point t of known dyadic order d, a valid coset b+<t> with db!=O, and coordinates of the function in the specified elliptic bases. Proposition 3 supplies a d log d straight-line evaluation bound for that coordinate input. The reduction problem likewise starts with coordinates of its function. It does not compile an arbitrary implicit long product into a d~J coordinate vector.

The report correctly identifies both the torsion/coset/basis promises and the missing reduction/acquisition of F. No blanket objection to elliptic algorithms is claimed. The official [arXiv record](https://arxiv.org/abs/2510.27375) confirms the 18 March 2026 revision and says “To be published in Journal of Complexity”; the report accurately uses forthcoming publication wording.

## Moroz--Schost: explicit polynomial inputs for truncated resultants

Inspected the saved abstract/introduction, normalization model over K[x]/x^k, and Theorem 1. It accepts P,Q in K[x,y] with degree bound d and computes Res_y(P,Q) modulo x^k in soft O(kd) field operations, under characteristic zero or at least k. Half-gcd, normalization and initial-condition work operate on the supplied polynomial coefficient representation. Thus the report's degree-L cost/input issue for direct Res(F,D), and its caution that a one-point channel vector is not a supplied small polynomial, are accurate. A new paid low-degree resultant representation could change the application; it is not ruled out. No field normalization is silently licensed modulo a composite.

## Puchinger--Wachter-Zeh: Frobenius-linearized, not multiplicative q

Inspected section 2 finite-field/normal-basis conventions and linearized composition law, Table 1, and section 3.3/Theorem 12. The symbol q is a known finite-field cardinality; a linearized polynomial has exponents q^i, coefficients in the supplied extension F_(q^m), and multiplication is composition. The nearlinear specialized q-transform uses its stated subfield/normal-basis setting (including s dividing m). General multiplication/evaluation bounds have different degree dependence. These are not algorithms for the supplied multiplicative unit gamma^(m^2) or an automatically induced automorphism of the original target quotient.

The report's fixed-carrier automorphism warning is correctly unweighted: t->qt descends only for a q-invariant target set, impossible for a nonempty J<R set in the actual subgroup. Weighted, moving-carrier and larger-field alternatives remain open. This does not contradict the independently paid interpolation q-shift on canonical degree<J representatives.

## Overall applicability and status

The four inspected theorem interfaces do not currently yield the missing mixed diagonal/common-gcd acquisition from the paid rational-Newton actions. This is a bounded applicability finding, not an exhaustive literature theorem or scalar complexity lower bound. The already paid normalized quasiseparable operator is explicitly acknowledged. Spectral uniqueness is described as a separate obligation; the new cheap determinant/uniqueness check can discharge that branch without changing this report's mixed-output conclusion, and the report does not call it unpayable. No improved full-query clock or all-input/controller theorem is claimed.
