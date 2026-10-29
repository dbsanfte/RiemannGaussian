# Joint q-binomial sections as one acquired rational-Newton transform

26 October 2026. Paper-only direct-contraction attempt; no repository edits, tests, numerical campaign, implementation or Lean. Inputs and existing bounds are the frozen [fast-projective packet](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-fast-projective-20261026/README.md). No bounded rational certificate or variable-block degree obstruction is used as a substitute for execution here.

**Result.** The section bank can be represented by ONE common rational-Newton evaluation operator, with its forward and transposed actions genuinely initialized in soft K. All factorial starts and the exact final tail are also acquired in soft K. The remaining scalar is a weighted diagonal of a product of these paid transforms with two Vandermonde transforms. Applying them to each root separately costs soft K²; the old full product engine remains better. Thus this is an exact joint-contraction test and a smaller initialized scalar interface, not a completed speedup. The unresolved diagonal is explicitly identified rather than supplied by a generic matrix-action theorem.

## 1. Fixed finite pairing

Let rho=q^-1, H=K², h=2K²+1, F=product_j(X-y_j), J<=K, and let ell be a supplied linear functional on B[X]/F. Both F and ell cost soft J to read. Define

    G_h(X)=product_(i=0)^(h-1)(1-rho^i X)=sum_(t=0)^h a_t X^t,
    b_t=ell(X^t mod F),
    a_0=1, a_(t+1)/a_t=(rho^h-rho^t)/(1-rho^(t+1)).

The target scalar is S=sum_(t=0)^h a_t b_t. The geometric differences through h+1 are actual supplied units, so all factorial expressions below are lawful over the composite coefficient ring. No hidden q order is used.

Choose B=K and M=2K. Then BM=h-1. Every index 0,...,h splits into full blocks t=Bs+e, 0<=s<M, 0<=e<B, and the **two actual tail indices h-1,h**. Set A=rho^h, Z_s=rho^(Bs). Directly multiplying the coefficient ratios gives

    a_(Bs+e)=a_(Bs)*K_s,e,
    K_s,e=A^e*(A^-1*Z_s;rho)_e/(rho*Z_s;rho)_e.    (1)

All denominator exponents are Bs+1,...,Bs+e<=h, hence certified units. The exact finite joint sum is

    S=sum_(s<M,e<B) alpha_s K_s,e b_(Bs+e)
        +a_(h-1)b_(h-1)+a_h b_h,
    alpha_s=a_(Bs).                              (2)

This keeps the finite tail. It does not replace the actual rho by an auxiliary root of unity.

## 2. ALL block starts alpha_s are actually acquired in soft K

There is no separate q-factorial oracle for each s. Build the one degree-B polynomial

    C_B(T)=product_(r=1)^B(1-rho^r T)

and evaluate it at T=Z_s, 0<=s<M, by monic multipoint evaluation. This costs soft(B+M). Prefix multiplying the values gives f_(Bs)=(rho;rho)_(Bs), for all 0<=s<=M. Since h=BM+1,

    f_h=f_(BM)*(1-rho^h),
    f_(h-Bs)=f_(B(M-s))*(1-rho^(B(M-s)+1)).

Thus all three factorials in

    alpha_s=(-1)^(Bs)*rho^[Bs(Bs-1)/2]*f_h/(f_(Bs)*f_(h-Bs))

are paid. Their inverses are certified by the original short-unit screen, not by a new generic field argument. All powers have O(log N)-bit exponents; arrays and binary powering cost soft K. This acquires every alpha_s without emitting h coefficients or JB section numerators.

The two tail a-values use the same factorial formula or the last coefficient ratio. The b-tail is acquired from X^(h-1) mod F and one multiplication by X, followed by ell. Binary modular powering costs soft J log h, so the exact tail in (2) is also soft K. The first J b-values and their proper rational numerator are directly acquired from ell and rev(F).

## 3. The common section kernel has cheap forward AND transpose action

For any supplied vector c_e, consider (Kc)_s=sum_(e<B)c_e K_s,e. Let

    Q(Z)=product_(r=1)^(B-1)(1-rho^r Z),
    P_c(Z)=sum_(e=0)^(B-1)c_e*A^e
           product_(r=0)^(e-1)(1-A^-1*rho^r Z)
           product_(r=e+1)^(B-1)(1-rho^r Z).

Then exactly

    (Kc)_s=P_c(Z_s)/Q(Z_s).                       (3)

The degree of each polynomial is at most B-1. A balanced divide-and-conquer mixed-prefix/suffix conversion acquires P_c in soft B, without rational coefficient inversions. Explicitly, for a split at m, multiply the left partial sum by its missing suffix of denominator linear factors, multiply the right partial sum by its missing prefix of numerator linear factors, and add. Products at each depth have total degree O(B). This is the same classical product-tree basis-conversion mechanism, now applied to the complete section kernel rather than separately to each section.

Acquire Q and all Q(Z_s) once. Their factors have positive exponents at most B(M-1)+B-1<h, so every value is a certified unit. Monic MPE of P_c and multiplication by the known inverses give (3) in soft(B+M)=soft K. Reversing this explicit linear circuit gives K^t action with the same asymptotic cost. Only actual scalar inverses Q(Z_s)^-1 appear, all certified; no difference between evaluation nodes or possible native collision factor is inverted.

This is a genuine initialized **joint operator**, with O(K) stored product-tree data up to logarithms. It improves the *description/action* of the section bank over emitting JB section numerators. It has not yet contracted the particular two-index argument b_(Bs+e), which depends on BOTH indices.

Primary context checked: Bostan–Schost, [*Polynomial evaluation and interpolation on special sets of points*, J. Complexity 21 (2005), 420–446](https://cs.uwaterloo.ca/~eschost/publications/BostanSchost.pdf), introduction, basis conversions and transposition discussion. That paper credits the older fast Newton-conversion machinery and derives special geometric transforms. Here the mixed rational basis, its cleared conversion and every inverse guard are proved above over the actual ring; field-only interpolation hypotheses are not silently transferred. No new theorem for the final diagonal is cited.

## 4. Execute the joint readout on the now paid separated branch

The current native separation theorem supplies, on the good-family attempt, a factor or global units F'(y_j) in soft J. Thus the spectral weights lambda_j with

    b_t=sum_j lambda_j y_j^t

are actually acquired in soft J. For example if sum b_t z^t=P(z)/rev(F)(z), then

    lambda_j=P(y_j^-1)*y_j^(J-1)/F'(y_j).

Monic MPE, supplied unit roots and the certified derivatives pay all these inverses; a wrong-family failed separation attempt may be declined, while one good family is guaranteed to pass or factor.

Define the explicitly known Vandermonde operators

    V1(e,j)=y_j^e,              0<=e<B,
    VB(s,j)=(y_j^B)^s,         0<=s<M.

Both their forward/transposed actions cost soft(K+J), using ordinary multipoint evaluation and weighted power-sum rational series. Powered roots may coincide; neither forward MPE nor weighted power sums needs their separation. Then (2)'s full-block scalar is EXACTLY

    sum_j lambda_j * [ VB^t *diag(alpha)*K*V1 ]_(j,j).       (4)

Every factor and every single action in this expression is now paid in soft K, with the full finite endpoints and native inverse guards. Equation (4) is not a determinant or a supplied dense matrix; it is the exact weighted diagonal remaining after the strongest straightforward joint Newton conversion.

**Actual completion.** For each j acquire the length-B geometric column V1(:,j), apply K by (3), and take its scalar pairing with alpha_s*(y_j^B)^s. Sum with lambda_j and add the paid tail. This costs

    soft O(J*(B+M)+K)=soft O(JK+K),

hence soft K² in the native J~K regime. A transposed order of these actions has the same bill. Forming the entire J-by-J middle matrix is unnecessary but does not have a cheaper supplied algorithm here. One cannot replace its weighted diagonal by a product of the unweighted sums: the row and column use the SAME y_j.

This is the precise point where fast matrix actions fail to automatically imply a fast scalar contraction. It is an interface/cost calculation for the executed route, not an output-size or arbitrary black-box lower bound. An algorithm computing (4) jointly at soft K would be a genuine advance; none has been established by the basis conversion alone.

## 5. Relation to previous paired-diagonal work and the nonlinear outputs

The journal's [old terminal norm/composition audit](/home/dbsanfte/riemann/formal/docs/semiprime-factorisation-investigation.md:41990) already distinguishes a fast linear action from a paired diagonal/nonlinear norm. The old q-binomial C/C^t audits likewise do not furnish free paired evaluations. They retain prior credit. The additional concrete result here is the exact ONE rational-Newton section operator with **all its full-block coefficient starts and tail acquired**, and the explicit diagonal (4) it leaves. It is not counted as a new whole-query algorithm.

The scalar S is linear in ell. If a proposed soft-K algorithm for it is a linear straight-line circuit in the supplied functional coefficients, with unit constant divisions and preprocessing independent of ell, transposition recovers the coefficient vector g=G_h mod F at the same cost. This explains one useful positive consequence of solving this precise pairing: the remainder and then the two directional norms would be paid. It is not a lower bound, and it does not say a direct nonlinear projective-ratio algorithm must acquire g.

For the requested directional norms/cofactor ratio, the known safe completion remains the existing geometric product engine followed by soft-J postprocessing. No step above supplies the derivative-of-norm statistic from a single arbitrary linear projection. The best complete weighted query stays soft K^(5/4), while the uniform two-monic fallback stays soft K^(3/2).

## Next exact algorithmic target

The section parameters are not intrinsically separate: their common rational-Newton action and its transpose are paid in soft K. What remains is the weighted SAME-ROOT diagonal (4), or a direct projective norm variation exploiting the actual two-monic roots. This is a tighter joint-contraction input than an emitted JB bank, but the executed completion costs K² and does not improve the baseline. A future fast trace/diagonal algorithm must initialize this particular scalar, not merely reuse the already paid factor actions or drop its same-root correlation.
