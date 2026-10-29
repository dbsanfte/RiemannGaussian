# Retuned geometric sections and implicit composition: executed action budgets

26 October 2026. Scratch paper derivation; no code, experiments or repository edits. Read frozen direct-contraction/qbinomial-joint.md and composition-hybrid.md and primary NSSV2601.17422v2 (4 September2026, cached nssv.pdf/nssv.txt), Proposition3.1, Lemma2.7 and §3.1. **No faster completed selector is obtained.** The smaller graph makes explicit short-input composition comfortably affordable, but that affordability is prior credit (including composite-ring KU/spiroids), not a new NSSV consequence. An adjoint Sylvester contraction and an exact quotient reduction are executed below to locate the still-unpaid matched operation.

## 1. Actual retuned input and finite startup

Original prepared budget K, retuned conductor K'=Theta(K^(2/3)), J≤phi(K'), h≤O(K²). Use actual row separation/factor gates and the true common parity-rebased clock q. Put rho=q^-1, B=K, h=BM+r, 0≤r<B. Define

    G_h(X)=prod_(i<h)(1-rho^i X)=sum_(t=0)^h a_t X^t,
    C_(s,e)=a_(Bs+e), 0≤s<M, 0≤e<B.

The omitted tail is EXACTLY t=BM,...,h, of length r+1. The old specialized h=BM+1 formula is not copied with a missing endpoint.

All starts and coefficient tails remain acquired in soft K. Build the degree-B block polynomial prod_(v=1)^B(1-rho^v Z) and evaluate it both at rho^(Bs) and rho^(r+Bs). Prefix multiplication gives the factorials at Bs and r+Bs; the degree-r initial block initializes the latter. These supply f_h,f_(Bs),f_(h-Bs) and hence each a_(Bs). The tail coefficients follow by r actual unit coefficient ratios. All exponents are O(log N)-bit labels. No h-array is supplied.

The same rational-Newton conversion gives C and C^t scalar actions in soft(B+M)=soft K, with actual unit denominators. The tail polynomial modulo the acquired degree-J row polynomial costs soft(K+J), by monic reduction and one modular power. This extends the frozen initialized action to the actual h, without requiring an artificial length.

Take U_j=y_j^B. Original K-rough orders make B=K powering injective in every relevant local subgroup. Thus the actual row-separation continuation supplies all U differences as units. Acquire f_B(U)=prod(U-U_j), H(U_j)=y_j and its unit inverse graph in soft J. Here no unknown inverse exponent or field Frobenius is used.

## 2. Smaller explicit core: useful but already paid classical scope

If an explicit O(J)-coefficient small representative of the graph polynomial were supplied, NSSV's generic field exponent J^((omega+3)/4) is at most K when J≤K^(2/3), even with omega=3. This is NOT first affordability: journal29631–29643 and42024–42035 already audit Kedlaya–Umans composite-ring composition and the stronger deterministic arbitrary-Z/N spiroid explicit-input bound J^(1+o(1)). That classical explicit core also fits the retuned budget. No native genericity hypothesis is needed to justify this conditional affordability if the previously audited general-ring algorithm is used.

But the input here is the implicit K-by-K coefficient bank C, not an acquired O(J) composition polynomial. That structured-input reduction is separate from running any short-input core.

For comparison only, even granting free reduction of every U-column modulo f_B, direct NSSV Proposition3.1 has m≈J, d≈K, mu≈K^(1/3), and favorable delta≈J/mu. Its bound mu^omega(delta+m mu) is soft(K^(1+omega/3)) in the maximal-row regime J=Theta(K^(2/3)), not softK. Lemma2.7 instead requires first-variable width<mu; it does not apply to the original width K merely because its reduction oracle has cheap actions. The exact hypothesis and input cost must both be preserved. These field/generic direct bounds are comparisons, not a licensed native fallback.

## 3. Execute matched diagonal, with the actual number of calls

For a supplied linear functional ell, acquire spectral coefficients lambda_j with ell(X^t modF)=sum_j lambda_j y_j^t, using the actual derivative gates. Then the full-block scalar is

    sum_j lambda_j [V_B^t diag(alpha) K_newton V_1]_(j,j).

Each single action is initialized softK. Executing this factorization uses ONE column action per j, plus its explicit pairing and tails: J calls, total soft(KJ+K), at most softK^(5/3). If derivatives are wanted, differentiating the supplied column/pairing circuits adds a constant number of such actions per j. One may then assemble physical product first jets and use the existing unique-row consumer, but this does not improve the cost.

Transposing the circuit does not reduce the number of matched columns. This is the cost of the executed factorization, not a lower bound for a new scalar-only algorithm. The old direct geometric engine remains better at soft(J+sqrt(Jh))≤softK^(4/3), while keeping the original unretuned family retains softK^(5/4).

## 4. A direct rank-one Sylvester/adjoint attempt, including all its unit pivots

Use the acquired finite displacement

    C L-Z C R=d v^t,
    L=S-rho^h I, R=(rho S-I)diag(rho^e),
    Z=diag(rho^(Bs)).                               (1)

Here S is the lower shift. For general h the last-column generator is still obtained from the ACTUAL next coefficient a_(B(s+1)), including the start of the paid tail. There is no boundary omission.

Let E_(s,e)=sum_j lambda_j (y_j^B)^s y_j^e be the matched contraction. Solve the adjoint equation

    L Q^t-R Q^t Z=E^t.                              (2)

Then cyclic trace transport gives the exact scalar identity

    <C,E>=trace(C E^t)=trace((CL-ZCR)Q^t)=v^t Q^t d. (3)

This really reduces the final output to a rank-one boundary pairing. It does NOT by itself compute Q. Column s of Q^t solves

    (L-Z_s R) q_s=E_(s,:)^t.                        (4)

The matrix is bidiagonal. Its diagonals are -rho^h+rho^(Bs+e), all actual short-gap units (the exponent difference is h-Bs-e>0 on the full rectangle), and its adjacent coefficients are explicit powers. Thus (4) is an initialized, denominator-safe recurrence; no generic Sylvester pivot or field inverse is assumed.

Two actual completions are available. Solving all M recurrences directly costs MB=Theta(h). Exploiting E's supplied sum of J geometric outer products invokes the same rational-Newton transform once per j, costs J soft-K actions, and returns (3) in softKJ. The rank-one forcing has not supplied a closed scalar recurrence for Q's matched boundary. In particular E is an acquired rank-J FACTORIZATION, not an acquired dense M-by-B array, and cannot be replaced by its unweighted row/column sums. This is a specific attempted boundary solve, not a generic displacement-rank objection.

## 5. Execute quotient compression and identify its finite correction

Let f=f_B and gamma=rho^B. An attractive idea is to reduce every column before using(1). For any column polynomial p write p=r0+f t. The exact graph shift is

    p(gamma U) modf = r0(gamma U)+f(gamma U)t(gamma U) modf. (5)

The smaller graph does make some additional scalar preprocessing affordable. Acquire

    r_f(U)=f(gamma U)-gamma^J f(U), deg r_f<J.

With the f-adic expansion p=sum_(k<d) f^k p_k, deg p_k<J, d=ceil(M/J), equation(5) becomes

    p(gamma U) modf =sum_(k<d) r_f(U)^k p_k(gamma U) modf. (6)

In the maximal-row regime d=O(K^(1/3))=O(sqrt J). Uniformly Jd≤M+J=O(K), so all r_f^k modf are explicitly precomputed in soft(Jd)=softK even when J is smaller. A supplied scalar column polynomial is converted to its f-adic digits by divide-and-conquer division by acquired monic powers of f, in soft M work. The formula is exact, including the quotient correction, and uses no invariance of the finite root ideal under scaling.

For ONE supplied column combination, f-adic division, shifts and (6) are already softK, as is the frozen boundary action. For the special C columns weighted by the SAME graph H(U)^e, what is needed is the jointly acquired contraction

    sum_e sum_k r_f(U)^k p_(k,e)(gamma U) H(U)^e modf,       (7)

where p_(k,e) are f-adic digits of g_e(U)=sum_s C_(s,e)U^s. Those digits for all e are not supplied by the powers r_f^k. Scalar-vector C-actions give any ONE prescribed constant combination in softK. Running them for a graph coefficient basis gives J calls and returns to §3. Evaluating a constant-vector circuit over a rank-J coefficient algebra likewise charges that rank. Equation(7) is exactly the structured polynomial-coefficient reduction needed BEFORE the affordable explicit core.

Thus the new aspect ratio permits a small shared list of quotient multipliers, but it has not acquired their correlation with the special input columns. The formula does not assert that those columns have full rank or that their corrections are independently arbitrary. A one-pass contraction exploiting their rational-Newton structure could still solve(7).

## 6. Scope, gates and exact next operation

All actions, graph interpolation, starts, tails, unit bidiagonal pivots and quotient multipliers above are initialized using monic arithmetic and actual short-gap screens. Degree-J scalar operations have polylog(N) bit overhead; label exponents remain O(log N). Actual nonunit row/shift leaf gates localize and use the once-only original soft-K extractor. Auxiliary relation pivots that are not actual leaf relations must instead be unit-certified or declined; their saturation is not assigned that decoder.

No weak row-selector is obtained from one arbitrary linear projection of G_h: that would require an additional selected-pole or product-jet identity. If (7), or the equivalent adjoint boundary in(3), were acquired in soft(K+J^(3/2)) together with a proved route to the physical weak pair, the retuned row-index consumer would complete factor recovery in softK. A linear straight-line evaluation valid for arbitrary ell would also give G_h modF by transposition, but this consequence is not assumed for a nonlinear selected-ratio method.

The surviving missing operation is a STRUCTURED-INPUT matched reduction, not short-input composition itself. The executed Sylvester method has unit pivots and a scalar output formula, but its known completion still uses J actions. The quotient formula exposes an affordable shared multiplier list and the remaining correlated digit sum. No new complete query rate, general lower bound, or native genericity claim is made.
