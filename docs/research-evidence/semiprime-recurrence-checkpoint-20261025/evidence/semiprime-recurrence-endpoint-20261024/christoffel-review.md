# Independent finite-geometric Christoffel review

24 October 2026. Reviewed exact current bytes of /tmp/semiprime-recurrence-endpoint-20261024/christoffel-terminal.md.

SHA-256: `c523fc8a1a7a23d667f32714e1671c6eb782b52d423984681402eb8deea01008`.

Verdict: **PASS. No required fixes.** This is a read-only mathematical and acquisition audit; no repository changes, finite examples or new backend claim.

## Full-support normalization and unit safety

With V_(r,i)=x_i^r, the two matrix identities H_1=VV^t and H_F=V diag(F(x_i))V^t hold over every commutative ring. Thus det(H_F)=det(H_1)*product_i F(x_i), with no pivot assumption. Unit differences of the actual q seeds make V and det(H_1) invertible. This certifies the normalizer's unit status even at target hits; it does not invert the weighted matrix or its determinant.

The explicit Vandermonde formula checks: extracting q^i from q^j-q^i contributes exponent sum_(i<j)i=binom(L,3), while each difference q^k-1 occurs L-k times. Hence the stated Delta and Delta² normalization are correct. Directly acquiring all L-1 weighted q-difference factors costs soft L. The report correctly distinguishes this cost from the fact that support detection can omit the numeric value of a certified unit normalizer. It does not label the full determinant acquired merely because this normalization is known symbolically.

For n>=1, the moment formula uses only 1-q^n as denominator; the upper index 2L+J-2 is inside the stated inherited guard. mu_0=L is supplied separately. The nu list is exactly a cross-correlation of the acquired f_k and mu list, so all required full moments cost soft(L+J); only an O(J)-sized initial moment list is cheap at soft J. Numerator zeros are never inverted. Shifted seed intervals require the corresponding known q^a coefficient scales, which are paid and do not change the difference-unit or complexity arguments.

Over a hidden field, V invertible implies rank(H_F)=L-c_p. Since q seeds are distinct and F has degree J, c_p<=J. This is a property of the actual full matrix, not a scalar-algorithm lower bound. The smaller d-by-d Cauchy-Binet formula is also correct; deleting one seed's weights removes only summands containing that seed. There is no universal factor-of-every-hit identity for the cheap truncated Gram determinant supplied by this formula.

## Compact displacement is actually initialized, but its full generator arrays are not free

The descriptor construction uses exact cofactor polynomials A/(1-q^kX), so rational-addition/product trees acquire A,P,Q in soft J without evaluating a dangerous denominator. Their degrees are J+1,J,J as claimed.

For n>=1, substituting the geometric moment formula directly gives

    A(q^n)*nu_n
      =sum_k f_k*A(q^n)/(1-q^(n+k))
       -q^(Ln)*sum_k f_k*q^(Lk)*A(q^n)/(1-q^(n+k)),

which is precisely P(q^n)-q^(Ln)Q(q^n). At n=0, the k=0 terms agree and cancel and every other cofactor evaluates to zero, so both sides vanish. It is correct and essential that nu_0 is not obtained by dividing this equation by A(1)=0.

The generalized displacement follows entrywise at n=r+s. Each monomial q^(t(r+s)) is the outer product v_t v_t^t; the second sum shifts t to L+t. Thus the rank bound 2(J+1) and displayed signs are correct. The scalar polynomial descriptor is soft J, but emitting 2(J+1) length-L geometric generators costs O(JL) entries. Alternatively standard Hankel boundary generators require the full length-L moment lists, acquired at soft(L+J). Neither input contract is silently replaced by a compact formula. A different determinant algorithm accepting implicit geometric generators remains explicitly open.

## Degree-L null boundary and exact alternant

P_L is the monic null polynomial of the full unweighted finite measure because it vanishes at every seed. It may be continued by the chosen null tail X^rP_L without inverting singular moment pivots. This is a direct construction, not an assumed nonsingular infinite orthogonal recurrence. Possible nonunit earlier Hankel pivots are also correctly acknowledged; seed separation alone does not license them.

The determinant of M_(r,j)=Y_j^r P_L(Y_j) factors as V_Y*product_j P_L(Y_j), with V_Y=product_(j<k)(Y_k-Y_j). Reversing the LJ factors x_i-Y_j yields the exact (-1)^(LJ) sign in E_L. Target separation makes V_Y a unit, but the actual completion avoids computing its numeric value altogether. The identity is valid over Z/N even at desired zeros and does not rely on quasi-definiteness of a source theorem.

The diagonal P_L(Y_j) remains unacquired in this formula. The report does not infer that every possible scalar determinant algorithm must reconstruct it: it states only that the displayed alternant and short descriptor do not initialize such an algorithm. This is the correct limited boundary claim.

## Scalar completion and all recovery costs

The common B_b(X)=product_(r<b)(X-q^r) is explicit. In seed block k,

    product_(r<b)(Y_j-q^(kb+r))
      =q^(k*b²)*B_b(q^(-kb)Y_j).

Thus its starts, unit scales and tails give exactly P_L(Y_j). Constructing degree b and evaluating at J*floor(L/b) acquired points costs soft(b+JL/b+J), optimized to soft(J+sqrt(JL)); monic MPE does not need cross-difference inverses. The final sign matches the alternant. Scalar output can stream the products without constructing a J² matrix.

Restrictions preserve actual row/index labels and the same constructor. Proper gcds factor; saturated products descend by paid row/interval restrictions to an original scalar-beta leaf, where the existing bounded global decoder applies. No arbitrary Christoffel or Hankel pivot is inverted. A hypothetical faster determinant is not granted these witness guarantees automatically.

## Claim scope

The report faithfully identifies an initialized short descriptor, the full compatible-data acquisition charges and the collapse of the finite-support orthogonal boundary to the grid polynomial. Its actual terminal algorithm remains the inherited soft(J+sqrt(JL)) routine. It claims neither a soft(J+sqrt L) endpoint operation nor a general lower bound against scalar algorithms, and obtains no factoring exponent gain. The exact reviewed bytes pass.
