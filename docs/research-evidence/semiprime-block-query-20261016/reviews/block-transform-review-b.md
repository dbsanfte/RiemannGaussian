# Independent review B: paid block transform and arbitrary binomial remainder

2026-10-16. Verdict: PASS. These are actual paid positive primitives; they do not yet acquire the original target remainder or factor-only query.

## Exact reviewed bytes

- `/tmp/semiprime-decimation-query-20261015/block_transform/report.md`: 8629 bytes; SHA-256 `825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70`.
- Adjacent manifest: 1476 bytes; SHA-256 `9384a43ac616cbe07cf032db385c984b74e9b56088a7adfee680ed128abcf90f`.

The report entry and all FIVE prerequisite entries in that manifest independently match their recorded byte lengths and hashes. The selected-coefficient, formal reverse-mode, decimation and actual-source premises were checked against their exact reports. No source report or repository file was changed; no build was run.

## 1. Block operator and formal transpose

The coefficient recurrence is correct, including sign and q-power normalization. At a supplied complete row start a_j, the quotient c_(a_j+s)/c_(a_j) need not be formed: the exact relation is c_(a_j+s)=c_(a_j)R_s(q^(a_j)). Its only inverse factors have exponents a_j+1 through a_j+B-1, all within 1,...,L. Thus zero coefficients would not invalidate the recurrence implementation, and no collision value or c_k is inverted.

The upper triangular matrix T_s maps y to v_s+(A_s/B_s)y. Ordered multiplication T_0 T_1 ... T_(B-2) on the terminal value v_(B-1) gives exactly the displayed nested rational-Newton sum with denominator Q. Off-diagonal entries remain formally linear in the weights. Divide-and-conquer multiplication, monic multipoint evaluation (including repeated points), and batch inversion of the parameter-only Q values cost the stated soft O(B+nu), after the paid selected c_(a_j) setup. B=1 gives Q=1 and N_v=v_0 without an exceptional inverse.

The complete setup includes selected coefficients soft O(sqrt L+nu), q^(a_j) powering, q^L and short q-power lists, and the unit inversions. All inverse constants are independent of formal weights. Therefore reverse differentiation of the arithmetic straight-line program for sum_j w_j(Cv)_j returns C^T w over R, at a constant gate overhead and comparable stored-residue cost. Numerical agreement on a finite ring is not substituted for formal linearity. Polynomial multiplication/evaluation in this formal argument uses ring arithmetic with parameter-only known-unit constants; bit encoding may separately justify its modular bit cost, but no weight-dependent carry operation is silently differentiated.

## 2. Ragged rows and one-binomial remainder

T=floor((L+1)/B) complete rows use only indices <=L. The final h=L+1-BT<B coefficients are separately selected within the same original range; no 1-q^(L+1) or later denominator is required. The resulting r_s are exactly the coefficients of F modulo the monic t^B-X, for every X, including zero and nonunits. The powers X^n and X^T require no inverse. If T=0 the complete-row operator is empty and the partial row supplies the whole degree<=L polynomial; its cost is absorbed by B. If h=0 no partial call is needed.

Hence soft O(B+L/B+sqrt L) work/storage is correctly charged. At B~sqrt L this genuinely acquires a FULL degree<B remainder in soft O(sqrt L), rather than only giving a formal identity for one. In the intended polynomial-size regime its modular bit cost is soft O((B+L/B+sqrt L)log N).

## 3. Fraction-free cofactor at arbitrary X

D_h(u)D_h(-u)=D_(h+1)(u^2) for dyadic node powers, with no sign error under the convention product(1-u/z). Telescoping proves E_B(t)=product_h D_h(-t^(2^h)) as a polynomial identity over R. It does not divide by D in the binomial quotient.

In the downward recursion the child modulus u^(B/2^(h+1))-X pulls back under u->u^2 to the parent modulus u^(B/2^h)-X, so substitutions of quotient representatives are valid. Induction proves the advertised E_B remainder. A degree-J input polynomial reduces modulo each sparse monic binomial in O(J) arithmetic plus the explicitly paid powers of X. Reduced multiplication dimensions decrease geometrically; their sum is soft O(B), while denominator-level construction and repeated reductions cost soft O(J log B). Keeping all levels uses soft O(J+B) residues, with logarithms absorbed. B=1 correctly returns E_1=1.

The cofactor recursion itself performs no inversion. Initial unit-node reciprocals, if not already supplied with D, are ordinary public parameter metadata and must be acquired/charged; their soft O(J) unit inversions do not require factor knowledge. Crucially neither D_B(X), X, a derivative, nor a collision row value is ever inverted. Thus roots of D_B, saturated X and nonunit X create no omitted failure branch in this fraction-free primitive.

Multiplication of the two paid remainders modulo t^B-X gives ALL decimated numerator values N_(B,r)(X). The stated soft O(B+L/B+sqrt L+J) total includes their explicit B-element output and does not materialize the B-by-(L/B) coefficient matrix or full mask of degree J(B-1).

## 4. Scope of the positive outcome

The report correctly distinguishes ONE arbitrary coarse scalar X from J different powered target points. At X=z_j^B every channel transports the same original row payload up to known units; all B channels do not scan B different source rows. Fast scalar/transposed coefficient and mask operators alone do not compute the mixed diagonal. The promised source gives the coefficient-denominator units and known target metadata without supplying hidden orders to the algorithm. No improved full-query exponent, all-input branch guarantee, controller bit/memory theorem or Lean result is claimed.

This is paid positive progress: rational-Newton block application/transposition, arbitrary-binomial F remainder, and arbitrary-point entire Cartier vector. The simultaneous mixed contraction and factor-selective acquisition remain open.
