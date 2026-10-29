# Independent review: a generic-polynomial route avoiding Appendix D

26 October 2026. Active mathematical dependency audit, scratch only. Read the supplied ETH paper's Proposition3.4, Definition3.1, Lemma4.7, Lemma4.8 proof and AppendixB, printed pp21–26,33–35,47–50. **PASS for the stated Boolean-network reduction under the generic replacement-form/counting lemmas, with the explicit parameter verification and factor-evaluation accounting below.** This is independent of TheoremD.1's tensor recursion and does not use LemmaD.2, the sparse-incidence degree cap or parity lifting. It does not assert that an existing fixed-k Lean SAT endpoint already proves the new generic-polynomial corollary.

## 1. Actual polynomial factors and incidence degree

Let the Boolean tensor network have n=E one-bit edges. For each nonisolated vertex v of arity w_v, define its multilinear extension over Q by

    Phi_v(X)=sum_(a in{0,1}^w_v) T_v(a)
                         product_j l_(a_j)(X_j),
    l_0(X)=1-X, l_1(X)=X.                         (1)

Each T_v(a) is0 or1 returned by the supplied uniform polynomial-time entry program. Equation(1) agrees EXACTLY with the tensor on every Boolean port assignment. Thus sum_x product_v Phi_v(x|ports) is the integer contraction. All factors here are ordinary rational polynomials; no field conversion or modular zero-indicator is needed.

A wire belongs to its two endpoint scopes, so the maximum occurrence b=2 and total scope length M=sum_v w_v=2n. Parallel edges are distinct variables; the bipartite graph has no self-loop. Isolated scalar tensors are evaluated once and discarded if1, or terminate the count if0. There are at most2n remaining factors. Every Phi_v has degree at most w_v. Treating incidences as separate indeterminates, the product has degree d<=sum_v w_v=2n, which is the precise Proposition3.4 input hypothesis. A large individual scope does NOT change this global degree bound.

The factor is not supplied as an explicit list of its2^w_v terms, but Proposition3.4 charges its evaluator separately. The streaming evaluator in §3 is an actual algorithm for that input, not an assumed oracle for a dense polynomial.

## 2. Reuse the numerical parameters, not the hypothesis of Lemma4.8

Suppose w=max_v w_v<=c0*n^(3/4), with fixed c0. Set lambda=ceil(log2 n), nu=ceil(log2 lambda), and use the beta=1 numerical choices

    r=floor(sqrt(lambda)/nu²),
    Q=floor(lambda/(128nu)), R=4ceil(sqrt(lambda)),
    tau=1/(r lambda), D=r^(2Q).

Lemma4.8 ITSELF assumes w<=lambda, so cannot simply be cited with this larger w. Instead verify Lemma4.7 directly. For sufficiently large n, r>=2, R>=32,6R<=Q. Also

    D<=2^(lambda/128)<2^(1/128)*n^(1/128).

The harmless factor2^(1/128) comes from ceil(log2 n); literal D<=n^(1/128) is not needed. The first balance inequality is

    2(b+w)D²=O_c0(n^(3/4+1/64))<2n=M.

The second,2Qr²<=n, follows because its left side is polylogarithmic in n. Thus scope n^(3/4) fits this design; it was the balance inequality, not a theorem-wide prohibition on growing w, that needed checking.

Choose the source's length-R integer interval centered within one of the binomial mean mu=Q(r-1)/(2r). The same R>=32, R<=Q/6 argument makes it lie in[0,Q] and contain all integers within R/4 of mu. Hoeffding gives a tail at most2exp(-R²/(8Q)); these parameters give at most2exp(-256nu). This is eventually below

    tau/(r*b)=1/(2r²lambda).

The tail condition depends on b=2, NOT on w. All rational/integer inequalities can be checked exactly; when they fail at bounded sizes, use direct summation. Lemma4.7 therefore constructs the full Definition3.1 data in polynomial bit time/space in the displayed parameters. Constants depend on fixed c0, not on an unbounded clause-width parameter.

## 3. Evaluate a factor at the actual non-Boolean Taylor inputs

At each Proposition3.4 evaluation the inputs to Phi_v are explicitly acquired univariate truncated series theta_j(z) modulo z^J. They are generally NON-Boolean. Evaluating the0/1 tensor program directly on them would be invalid. The legitimate evaluator is (1): stream all2^w_v Boolean assignments a, call T_v(a), and multiply the w_v appropriate affine series l_(a_j)(theta_j).

The rows of Definition3.1 have common denominator

    dd=(R-1)! Q!.

Every theta_j has denominator dd; each affine series has the SAME denominator. Each term of (1) therefore has denominator dd^w_v, independent of a. Sum into that denominator; do not recompute a product of denominators for every truth assignment. Truncated series operations have polynomial dimension J and polynomial-bit coefficients by the bound below. One factor costs2^w_v*poly(n+description) bit work and polynomial working space. Its2^w_v terms are not stored. A w_v-bit enumeration counter, one term product and one accumulator suffice.

Let Btheta bound the coefficient1-norm of dd*l_(a_j)(theta_j), uniformly in j,a. Definition3.1's row coefficient bound and the Taylor shift at t<=Q give

    log Btheta=O(Q log Q+log n+R log(Q+1))
              =O(Q log Q+log n).                  (2)

Truncation cannot increase the coefficient1-norm; the binomial coefficients introduced by the Taylor shift are already included in the (Q+1)^R bound in (2). After normalization, a factor numerator has norm <=2^w_v Btheta^w_v. For ALL factors a full contribution has common denominator

    Omega=dd^M=dd^(2n),

and numerator norm <=2^(2n) Btheta^(2n), before group-assignment summation. Summing the group assignments contributes at most another2^n factor. Summing the Möbius pairs/measurement tuples contributes at most3^n(2D+1)^(2tau n). Hence every intermediate accumulator has polynomial bit length

    O(n(Q log Q+log n)+n).

For these chosen Q, Q log Q=Theta(log n), so this is also O(n Q log Q+n), as proposed. The denominator itself has O(n Q log Q) bits. The local2^w enumeration increases numerator bit length only by w, not by2^w. All products of group denominators divide the SAME Omega; no branch-dependent denominator explosion is hidden.

This is a direct analogue of AppendixB's fixed-denominator argument, with the simpler tensor multilinear factors replacing its parity polynomials. It does not depend on the mismatched AppendixB displayed degree formula: here the actual total degree is independently d<=2n, so d_H=2nR and J=floor(2nR/Q)+1 are used explicitly.

## 4. Total time, interpolation and polynomial space

Let eta=R/Q. The number of Taylor/Möbius pairs C_q, with q=floor(dR/Q), satisfies the paper's bound

    log C_q=O(n eta log(2/eta))
           =O(n nu²/sqrt(lambda)).

The measurement exponent2tau*n*log(2D+1) and group assignment exponent2n/r are O(n/r)=O(n nu²/sqrt(lambda)). Multiplying by the streamed factor evaluators therefore gives

    poly(n+description)
          *2^(O(n nu²/sqrt(lambda))+O(w)).          (3)

The stated w=O(n^(3/4)) is asymptotically smaller than the first exponent, but retaining O(w) makes its source explicit. This is a bit-cost bound, not just a count of operations on unspecified coefficients.

For final Hermite interpolation QJ=O(nR+Q) is polynomial in n. Its entries and the common-denominator Taylor data have polynomial bit length by §3. Fraction-free elimination / the AppendixB selected-constant-coefficient calculation consequently takes polynomial time/space in n. The recovered H(0) is an integer by (1); the final rational division is exact, not a nonunit modular inversion.

Process all points, correction pairs, measurement tuples, group assignments and local truth-table terms sequentially. Store only their counters/representatives, one factor product, one group sum, one global accumulator and the polynomially many Taylor data. Each stored series has J coefficients of the polynomial bit length above. Thus the FULL evaluator, not merely each entry program, uses polynomial space. There is no explicit tensor truth table, full polynomial in n variables or exponentially large output table in memory.

## 5. Consequence for the macro-FFT bridge, and formal scope

If the separately supplied multiplication encoding has n=Theta(L), maxscope w=O(L^(3/4)) and uniformly polynomial-time0/1 entry programs, substitute into (3). If only n=O(L) is stated, harmless independent forced-zero wires pad it to Theta(L), preserving the count, b=2 and the scope bound:

    poly(L)*2^(O(L*(log log L)²/sqrt(log L))
                    +O(L^(3/4))) = 2^o(L).

Canonical functional internal word assignments and the actual O(L) wire bound remain obligations of that encoding. Conditional pinning can be folded into a tensor entry predicate on an already incident bit, so does not require increasing the b=2 incidence bound. Standard count-based self-reduction adds polynomial overhead. This provides a second paper-lemma route to the conditional factoring conclusion, independent of the AppendixD mode contraction.

This does NOT follow merely by substituting k=w into the paper's fixed-k SAT theorem. Nor is it an automatic consequence of a Lean theorem proving only that endpoint. The formal handoff must instantiate the generic Q-algebra sum, incidence degree d<=2n, large-scope Lemma4.7 design, streamed non-Boolean factor evaluation and its bit/space bound. I have not asserted those new instantiations are already present in Lean. This review verifies the mathematical reduction and its charged interfaces; no frozen repository file or proof artifact was changed.

**Final assessment:** no blocker found in the proposed older generic-polynomial route. The essential corrections are to invoke Lemma4.7 with manually checked large-scope parameters, not Lemma4.8's inapplicable w<=lambda premise; to stream the TRUE multilinear extension at non-Boolean inputs; and to use the shared denominator dd^(2n) with actual bit bounds. Under those conditions the claimed subexponential-in-bitlength consequence is supported by these lower-level paper lemmas, independently of TheoremD.1.
