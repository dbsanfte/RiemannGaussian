# Independent audit of implicit digit/box encodings

24 October 2026. **PASS.** Exact final source reviewed: `/tmp/semiprime-implicit-thin-encoding-20261024/working.md`, SHA256 `84c8f8036a33637d6c05dc9e444c75f29ee98b4efe68f18d4d3b55b09d3b5435`. The earlier c6eebef4 draft received three scope precisions from the author: skip degree-D arrays in the large-stride branch, bound the auxiliary parity clock, and use the correct native Pochhammer argument throughout. The final source also includes the explicitly scoped natural-padding count. No required corrections remain. Reviewer changed no source, draft or repository file.

## Native convention and actual tensor forms

The corrected covered-block identity is exact: product_r(V_j-q^(ab+r))=V_j^b P_b(q^(ab)/V_j). All V_j are known units, so their explicit inverses and the common product of V_j^L are legal and charged. Full and tail block arguments retain the ORIGINAL j,block and bounded local index. The auxiliary negative pure clock is not substituted for those target-dependent arguments.

I checked the actual Section 2.2 p-hat/q-hat forms in the pinned primary PDF. The singleton and negative-pair INNER masks, zero restrictions, outer singleton rules and P0 outer sums match. Pure-power inner encoding factors digitwise exactly, with an actual repeated-fourth-power table. It does not factor the coefficient tensor, nor the active-Q outer-band sum. When only one Q is active, left pair masks have zero corresponding right inner masks and conversely, so only the four matching singleton products remain at each inner position. This particular restriction cannot claim the full shared tensor batching gain.

The coefficient formula and the selected-prefix/sparse-mask startup agree with the independently audited companion at source pin `300952af3de79e56b9c90d4fe02c756e640273a3e2db444010c0c79d7cb07400`. The prefix algorithm actually pays all full blocks, dyadic residual starts and monic MPE; its coefficient divisions use only supplied unit products. The non-parity support {0,8} and its eight-factor formula are correct. The companion's fixed-mask rational-series clock batch is correctly distinguished from all masks and all outer parameters.

## AP coefficient-box primitive, including all starts and the final term

From the q-binomial formula, the transition quotient is

    x^D*(-1)^D*q^(Dn+D(D-1)/2)
       *product_(v=0)^(D-1)(1-q^(b-n-v))
       /product_(v=1)^D(1-q^(n+v)).

Setting X=q^n and absorbing X^D into the numerator gives exactly A(X),B(X) in (3), with its stated sign and q phase. The source uses this as a CLEARED relation; neither w_n nor x is inverted, so zero/nonunit x and zero sums remain legal.

The numerator matrix maps (w,S) to (A*w,B*(w+S)); dividing only its certified B gives the next coefficient and preceding-prefix sum. Therefore rho transitions followed by adding w_rho produces the inclusive prefix through a+D*rho. The scalar denominator product is exactly f(a+D*rho)/f(a), using each exponent from a+1 through a+D*rho once. No denominator at an extra, unrequested final transition is used.

For D<=sqrt b, the dyadic length s is within a constant factor of sqrt b/D. The matrix block degree is O(Ds)=O(sqrt b), and its doubled product order B_s(Q^sX)B_s(X) is correct for column states. All dyadic coefficient arrays total soft sqrt b. There are O(sqrt b) full coarse blocks along the ACTUAL transition range floor((b-a)/D); MPE at their real starts and literal matrix prefix products acquire the coarse prefixes. At each residual size there are at most T actual requested starts; summing degrees and request counts gives soft(sqrt b+T). The required unit denominator prefixes and initial w_a are acquired with the same selected-prefix lemma. This is an initialized matrix product, not a unit-cost arbitrary-prefix oracle.

The corrected large-D branch explicitly SKIPS both degree-D arrays. It samples the fewer than sqrt b+1 residue coefficients directly, accumulates their sums, and answers the requested endpoints. Thus the claimed bound holds for the whole stated stride range. Interval sums are differences, never divisions by a possibly zero sum. For several residues or different x parameters the source retains the actual repeated costs; it does not charge one residue's budget for all of them.

## Full active-Q forms and literal output counts

Equations (6)--(8) retain the actual row/column block assignments, active-Q summation and digit ranks after restricting to Q. Outer P0 coordinates give genuine radix-three boxes; singleton coordinates fix digits. Decomposing into at most 3^s row intervals and at most sqrt D inner residues gives the stated direct soft(sqrt(D*b)+T_Q) bound. Clipping at coefficient b and counting descriptions, repeated assignments and endpoint unions are explicit. A sparse inner mask is not asserted to acquire the whole band form.

The h=19m layout, A_Q=binom(19m,m), N0=3^(18m), K0=floor sqrt(A_Q), grid restriction, and all-10^h unmodified preencoding count match the primary layout. For nontrivial m, the displayed inequality 10^h>K0*N0*D follows even from K0<=2^(h/2). Consequently the number of slots WRITTEN by that full encoding algorithm exceeds b+1. The source expressly limits this to that algorithm's output count, not distinct functional values, an information lower bound, or a prohibition on compressed/wanted-only transforms. The UNION of wanted encodings, their descriptions and their different weighted x parameters remains unpaid.

## Auxiliary parity clock and both terminal-output attempts

The negative-clock formulas follow by reversing factors 1-q^(-r) and 1+q^(-r). Their phases, f ratios and a=0 branch are correct. The final source now explicitly restricts a<=floor(L/b), so all prefix indices are <=L and all q² guards require only 2L<C. In the proposed b>k^(3/2) regime their full output list and all prefixes/phases fit soft k. These values are auxiliary; P_b(1)=0 is not decoded as an original collision.

The partial-output matrix identity (10) is exact but requires all Rb*K weighted partial entries before the column contractions. Under the explicitly stated NATURAL padding and full J=Theta(k) family, b in [k^(3/2),L] gives S=O(k²), D=O(k^(1/9)), and Rb*K=Theta(JL/D), at least of order k^(26/9). This is the actual requested-output ledger of that literal reduction, not a lower bound on a different packed or weighted-output operation.

The diagonal-fold identity (11) really produces the desired P_b(x_j) outputs. Its left input, however, is already a native-target-weighted residue polynomial, not the scalar coefficient matrix used earlier. One-x AP/box primitives do not supply all K such left inputs or their required leaf union. The source correctly retains both that acquisition cost and the near-quadratic K-square theorem bound, without asserting that every alternative packing fails. The pure clock formulas do not apply to the corrected general q^(ab)/V_j arguments.

Finally, every correct terminal value still needs the ORIGINAL restriction/leaf interface. Individual mask, box or partial-output zeros are not assigned a factor decoder. The report supplies genuine sub-b primitives but no whole shared encoding, weighted-output/product contraction, query exponent gain or generic lower bound. Exact final bytes pass.
