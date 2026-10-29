# All higher finite Macdonald responses are acquired: the remaining selector boundary

26 October 2026. Scratch paper-only derivation. Read the frozen residue-shortcuts README, content-cover and collective-character final section. **Positive acquisition:** the ENTIRE higher row-operator generating polynomial for the actual GP clock is computed in soft J, not by a dense J-by-J determinant. Its matrix action and transpose action are also initialized in soft J. These acquired responses do not yet isolate the unique collision row. No soft(J^(3/2)+sqrt h) selector or improved factoring exponent is established.

## 1. Actual matrices and gates

Let D(X)=sum_(s=0)^J d_s X^s, d_J=1, with actual supplied unit roots T_i, and let the clock be 1,q,...,q^(h-1). Use the consistently normalized actual base (including the padded parity base when applicable). Focus on h>J; the inherited engine handles h=O(J) in soft J. The original or retuned family has its original-K order/short-gap preparation; every gap through h+J used below must lie inside that proved margin. The conservative retuning m³<=K/1024 leaves this margin, rather than placing h at 16H.

Gate D'(T_i) by MPE. A nonunit row difference localizes to an actual mixed-label alias; after literal duplicate labels are removed, its pair of integer labels is nonzero. The existing decoder factors a saturated global alias, and proper gcds factor directly. Thus on continuation the row interpolation nodes are UNIT-separated in every component. This gate is essential: uniqueness only promises the hitting row is simple, not that every other row is.

Put b=q^(h-1), and gate the two actual boundary leaves T_i-b and T_i-q^-1 for every row. Their nonunits have original/one-step-extended short labels and the existing localization/decoder. A correct-bin endpoint witness is handled directly, rather than discarded. On continuation they are global units. In particular D(b) is a unit. All gates cost soft K with the once-only licensed extraction charged; they are not assumed free ring inversions.

The q-shift interpolation matrix is

    M_ij=L_j(qT_i),
    L_j(X)=D(X)/((X-T_j)D'(T_j)).                    (1)

The expression is polynomial evaluation; it does NOT require inversion of qT_i-T_j. A Cauchy-generator implementation may optionally use the previously proved adjacent-q alias factor-or-unit screen. Matrix-vector action is interpolation at T_j followed by evaluation at qT_i, hence soft J by product trees. Transpose action has the same bound by transposition of these supplied linear maps.

For the finite kernel Psi=product_(i,k)(T_i-q^k), the exact row-shift ratio is

    R_i=q^h*(T_i-q^-1)/(T_i-b).                      (2)

These are acquired GLOBAL units after the endpoint gates. Set A=diag(R_i)M. Neither A nor its J² entries need be emitted. Its action and transpose action cost soft J.

## 2. Higher operators and an explicit soft-J characteristic polynomial

For I subset {1,...,J}, |I|=r, the principal minors satisfy

    det M_(I,I)=q^(r(r-1)/2)
                product_(i in I,k notin I)(qT_i-T_k)/(T_i-T_k).

This follows directly from the Cauchy determinant, or by clearing the identity and specializing the polynomial Lagrange matrix. Consequently

    chi(u)=det(I-uA)

is exactly the generating polynomial of all finite first-family Macdonald responses, after dividing the shifted kernel by the unshifted kernel on the universal regular locus. The cleared identity is valid at the actual collision; no numerical division by the zero kernel is used.

More importantly, chi is explicitly acquired. Let V_ik=T_i^k, 0<=k<J. Since M=V diag(q^k) V^-1,

    chi(u)=det[ T_i^k*(1-u*q^k R_i) ]/det V.

Multiplying row i by T_i-b makes column k the evaluation of the polynomial

    p_k(X)=(1-u*q^(h+k))*X^(k+1)
                      -b*(1-u*q^k)*X^k.

These are bidiagonal in the J+1 monomials 1,...,X^J. Expanding by the single omitted monomial gives the exact finite formula

    chi(u)=1/D(b) * sum_(s=0)^J d_s*b^s
                     *(u;q)_s*(u*q^(h+s);q)_(J-s).    (3)

All signs have canceled: the alternant minor omitting X^s contributes e_(J-s)(T)=(-1)^(J-s)d_s, while the lower coefficients contribute (-b)^s and the row denominator product is (-1)^J D(b).

As a hand control, J=1 gives

    chi(u)=[d_0(1-u*q^h)+b(1-u)]/D(b),

which is exactly 1-u*R_1. No native coverage example is used for this identity.

### Initialized conversion algorithm

Put w_s=d_s*b^s, A_k(u)=1-u*q^k, B_k(u)=1-u*q^(h+k). Acquire these O(J) linear factors by short powering. For an interval [l,r), form

    Q_[l,r)=sum_(s=l)^(r-1) w_s
               product_(k=l)^(s-1)A_k product_(k=s)^(r-1)B_k.

Balanced recursion is

    Q_[l,r)=Q_[l,m)*B_[m,r)+A_[l,m)*Q_[m,r),

with acquired interval products A,B. Add w_J*A_[0,J) at the root and divide by the certified unit D(b). Its polynomial multiplication cost is soft J, including all J+1 output coefficients. There is no degree-h input, unknown entry oracle, or J² dense determinant. Thus ALL higher row responses, not merely the first trace, fit even below the proposed J^(3/2) budget.

## 3. Clock-side suffix survivors, with their real denominators

The r-th Macdonald operator on the geometric Y alphabet has only ONE nonzero subset coefficient: the final r-element suffix. Every other subset contains i but not i+1, hence its coefficient has qY_i-Y_(i+1)=0. The surviving coefficient is

    q^(r(r-1)/2) * [h choose r]_q.

Its shifted kernel ratio telescopes to

    product_(i=h-r)^(h-1) D(q^(i+1))/D(q^i)
                          =D(q^h)/D(q^(h-r)).         (4)

This does not make the denominators automatically units. For all r<=J, acquire D at the J+1 end-strip points q^(h-J),...,q^h by geometric MPE in soft J. A nonunit in the original-clock portion localizes an actual endpoint-strip hit in soft K; it cannot simply be inverted. On continuation all original strip values are units, making (4) licensed. The q-binomial coefficients use gaps at most h, already covered by the actual screen. The numerator at q^h is merely evaluated; a nonunit there is not needed as a denominator.

Thus the higher dual responses also have a paid finite initialization, or a direct short-strip factor branch. They do not require scanning all h clock points. This is stronger than leaving every higher response as a symbolic h-variable operator, but it is only an endpoint-strip acquisition.

Primary reference: [Noumi, Kernel functions for Koornwinder's q-difference operators, page 2](https://www.maths.gla.ac.uk/island/island3/talks/noumi.pdf) states the finite type-II kernel and first intertwiner separately from the infinite type-I kernel. [Kirillov–Noumi, Affine Hecke algebras and raising operators for Macdonald polynomials, §1 equations (1.1)–(1.3)](https://arxiv.org/abs/q-alg/9605004) gives the higher subset operators and generating determinant. Formula (3), its conversion algorithm and the actual composite-ring gates are derived here; they are not claimed as complexity theorems imported from those sources. The earlier root-system and Schur-boundary audits retain prior credit.

## 4. Test the acquired spectrum as a selector

The actual unique collision does not make A singular. Since interpolation shift has determinant q^(J(J-1)/2),

    det A=q^(J(J-1)/2)*product_i R_i

is a certified unit. There is also no eigenvalue-one kernel: setting u=1 in (3) leaves only s=0 and gives

    chi(1)=d_0*(q^h;q)_J/D(b),

again a unit under the stated h+J short-gap margin. These facts concern this actual initialized matrix, not arbitrary fake native roots. In particular its easily acquired characteristic polynomial is NOT the characteristic polynomial of W_h(C), whose good component has the desired one-dimensional kernel.

The transformation (3) is triangularly invertible from short data: at u=q^-r, 0<=r<=J, all terms with s>r vanish and the remaining diagonal factor is a product of the screened q gaps (h>J). Thus chi is a finite basis transformation of the supplied row polynomial, with all coefficients paid; it has not imposed the additional finite condition W_h(theta)=0. This observation does not prove spectral processing of chi useless. It identifies what was actually computed and prevents an automatic substitution of its eigenvectors for the original pole mode.

To transfer a selected eigenvector or minor back to the original zero mode, one would still need an initialized relation selecting a clock-intersection branch. Formal conjugation by W_h at the row nodes is not licensed: at the good component its diagonal has a zero, and its actual values are the old long query. Principal minors of the acquired A are real higher-shift responses, not supplied cofactors of that singular diagonal or of W_h(C). Their q-shifted suffix formulas likewise inspect only the paid J-point end strip; they do not guarantee the unknown interior witness lies there.

At the retuned J=O(K^(2/3)),h=O(K²) aspect ratio, (3) is a genuine soft-K ALL-orders acquisition (in fact soft J after preparation). It still lacks a proved row-selector decoding rule. The retained complete query is the old shared engine. A new finite identity mapping these acquired all-orders responses to a nonzero good pole vector, without evaluating the singular W_h gauge, would be a substantive next step; no such map is assumed here.

## Addendum: explicit retuned gaps and first variations

For the retuned parity bank the actual base is Q=(pi^(H'))², H'=H/m². Hence Q^(m²)=q_orig². If Q^r were locally one, so would q_orig^(2r); the original q_orig unit-gap screen therefore certifies each required new gap r whenever 2r<16H. Algebraically, 1-q_orig^(2r)=1-Q^(m²r) is (1-Q^r) times a finite geometric sum, so its being a GLOBAL unit directly forces 1-Q^r to be a global unit. The conservative m³<=K/1024 bound gives the unthinned scaled horizon

    h <=(sqrt(2)/4)K²+9,

with the endpoint-gated parity clock shorter. Together with J<=K/3, this yields 2(h+J)<16H for native K>=54. Thus the h+J q-factorial gaps used in (3)–(4) are certified by ORIGINAL preparation even though N need not be <=(K')^6. In these formulas consistently substitute the ACTUAL Q for q; no smaller-scale order premise is imported.

The acquired response also supports a paid first variation of the short polynomial. For D_epsilon=D+epsilon E, deg E<J, and epsilon²=0, write E(X)=sum e_s X^s. Formula (3) gives

    delta_chi(u)=[sum_s e_s*b^s*(u;q)_s
                         *(u*q^(h+s);q)_(J-s)
                       -chi(u)*E(b)]/D(b).

The same balanced conversion acquires it in soft J, using only the already certified unit D(b). This is a genuine initialized jet of the ALL-orders response. It is not the pole residue of the long W_h query; nothing here guarantees this jet selects the good row.

Diagnostic replay: `check_higher_responses.py --output /tmp/higher-response-checks.json` uses only the Python standard library and naive polynomial multiplication. It compares the balanced conversion with a permutation-expanded dense determinant, independently summed principal minors and higher subset responses. Four fixed tiny algebra fixtures include known interior collisions, a composite ring with all required gates passing, and an additional exact q-adjacency qT_i=T_j where the division-free Lagrange numerator remains valid. The diagnostic does not require adjacent-q differences to be units. Recorded result: PASS, 33 checks. This validates finite signs/normalizations; it is neither a soft-J implementation nor a native coverage/factoring-success experiment.
