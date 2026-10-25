# Executed antipodal/inverse colour fusion for the quadratic source

24 October 2026. Scratch only. This attempt acquires the actual antipodal contraction and its group polynomials in soft k, then executes both the shared-seed and the normalized-center continuations. The former returns the paid degree-J, horizon-L query; the latter retains a varying family of starts. No uniform shrink of J times L, or faster terminal product, is proved. This is a scoped closure test, not a generic obstruction.

## Source and exact colours

Use frobenius-pairing.md, SHA256 215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363, and its independent PASS review, SHA256 147ed84ea489fb61e8e2b47e2c6d09a90cf247f743df017e48314b613f815a97. All discovery, both local beta/H-power margins, and same-leaf scalar-norm recovery are paid there. In particular D<0 is fundamental, chi=chi_D has conductor dividing even k, chi(N)=-1, and chi(-1)=-1. The explicit norm-one W and the prepared odd-order beta lie in the constant-rank algebra B=R[tau]/(tau²-D), bar(tau)=-tau. Put

    A=beta W, B0=bar(A)=beta/W, z=A^H, H=k²,
    n_j=N+a_j, E_j=n_j+ell_j,
    V_j=beta^E_j W^[ell_j+chi(j)n_j], L=2H+2.

Every actual V_j is already acquired in soft k total; no symbolic row list is priced as actual coefficients. Thus

    chi(j)=+1: V_j=A^E_j;
    chi(j)=-1: V_j=A^ell_j B0^n_j.              (1)

All unit tags are retained. Since a_j=N j^-2 modulo k and the character is genuinely periodic modulo k,

    chi(a_j)=-1 for EVERY row; a_j!=1.          (2)

This statement holds for composite k; it does not assert that the square-root map has fibers of size two. Its fiber size is mu=|U(k)[2]|, and the distinct a values are the coset N U(k)^2 of size phi(k)/mu.

The maps j->-j and j->j*=N/j modulo k commute, are involutions, and both reverse the colour. They send a to a and a^-1 respectively. No tag satisfies j*=j, by (2). The equation j*=-j is equivalent to a_j=-1 modulo k. Apart from such two-element orbits, their joint tag orbits have four elements. This is a bounded orbit size, not a growing orbit norm that removes O(k) rows.

## 1. Execute the antipodal contraction, including every mixed sum

Select the unique chi-plus tag j from each pair {j,-j}. With the actual centered convention,

    ell_j+ell_-j=H tau_j, tau_j in {-2,-1,0},
    a_-j=a_j, n_-j=n_j.

The two colours in (1) give the exact unit product

    V_j V_-j=c_(a,tau)=beta^[2(N+a)] z^tau.     (3)

Acquire S_j=V_j+V_-j as an ACTUAL pair of coordinates. Unlike the former rank-k Gauss attempt, ALL such mixed sums cost soft k here. At an indeterminate X,

    (V_j-X)(V_-j-X)=X²-S_j X+c_(a,tau)
                         =X*(X+c_(a,tau)/X-S_j). (4)

For every nonempty group g=(a,tau), acquire

    P_g(U)=product_(selected j in g)(U-S_j),
    r_g=degree P_g, sum_g r_g=phi(k)/2=J/2.

A product tree for all groups costs soft k; the total acquired degree is J/2, not the number of group names. At X=z^i, all divided factors are units except the intended differences, and the FULL family product is exactly

    product_(i<L) product_j(V_j-z^i)
      = z^[(J/2)L(L-1)/2]
        * product_(i<L) product_g P_g(z^i+c_g z^-i). (5)

The prefactor is an acquired unit. This is an initialized contraction, with all P_g and starts paid. It preserves every original leaf through (4); a nonunit contracted factor can be expanded to its two original leaves and passed to the source's norm controller. No nonunit square has been divided away.

The first retained terminal state is visible: the curved sequence z^i+c_g z^-i has a DIFFERENT c_g for each (a,tau), and P_g itself also varies. A product of the P_g is not evaluated at one common sequence. Applying the old blocked method independently to groups costs soft(sum_g(r_g+sqrt(r_g L))). When mu and the occupied r_g are bounded, there are O(k) groups and this ledger is O(k²), worse than the source's O(k^(3/2)) bound. The safe better continuation reconstructs the degree-J monic product from the acquired quadratics (4), in soft k, then uses the original common-z blocked query at soft(J+sqrt(JL)). Thus this executed fusion supplies a constant pair fold, not a new asymptotic gain.

## 2. Inverse pairing does not align those acquired centers by a common shift

The inverse-tag map replaces a by a'=a^-1 modulo k and swaps the two colours. Its second antipodal pair has center

    c_(a',tau')=beta^[2(N+a')] z^tau'.

These centers are genuinely different for different (a,tau), as can be checked from the PAID beta margins, without a generic independence assumption. Their norms are beta^[4(N+a)+2H tau]. Equality at the unknown nonsplit side would force

    beta^[4(a-a')+2H(tau-tau')]=1.

The exponent has magnitude less than 16H, while the local beta order exceeds 16H. It must be zero. Since |a-a'|<k and |tau-tau'|<=2, for the continuing k>2 this forces tau=tau' and a=a'. Consequently inverse pairs have no common center unless their actual group labels coincide. If a center-difference norm is nonunit, it is nonzero on the field side and therefore gives a proper factor; none is being cancelled merely because it is a unit descriptor.

There is an explicit square-root normalization of every center:

    d_g=beta^(N+a) A^(H tau/2), d_g²=c_g.        (6)

Here H is even, so no ring square root is extracted. Define R_j=V_j/d_g for j in pair-group g. Then R_j R_-j=1, but the original comparison becomes

    R_j = z^i/d_g.                              (7)

The reciprocal center has become common, while the START d_g^-1 varies by beta^[-(N+a)] A^[-H tau/2]. All starts are acquired in soft k; evaluating the resulting family is still unpaid. A common multiplicative change X->lambda X aligns two centers precisely by changing one group's start by d_g/d_h. It does not preserve a shared unshifted seed sequence for all groups.

The first combined four-row polynomial shows the same retained term without division:

    (X²-SX+c)(X²-S'X+c')
      =X^4-(S+S')X³+(SS'+c+c')X²
         -(S c'+S' c)X+cc'.                    (8)

Every coefficient is actually cheap now. But inverse-tag symmetry does not set c=c' or supply the extra relation between S,S' required to make this quartic reciprocal about one common center. Replacing these coefficients by formal orbit metadata would discard the term S c'+S' c. This attempt therefore keeps the full quartic, rather than crediting an unproved two-coordinate closed update.

## 3. Exact inverse-index carry: why dropping one colour is not covered here

One might keep only chi-minus rows, since the nonsplit prime has chi=-1. The source guarantee, however, is the SMALLER own prime P. The Jacobi condition gives opposite signs, not the sign of the smaller prime. If chi(P)=+1, its guaranteed small-index row is in the discarded class. At j*=Q modulo k the sign flips, but the swapped row has

    H I_Q=a' Q+P+ell_j*,
    a' I_P-I_Q=[(a'a-1)P+a'ell_j-ell_j*]/H.    (9)

The coefficient a'a-1 is divisible by k, not usually H. Formula (9) contains the unknown P; its full integer shift is not acquired by knowing residue j or the two character signs. The available inequalities give I_Q=O(k³), using Q<k⁴/16 and a'<k, whereas the guaranteed source uses L=O(k²). No O(k²) bound for I_Q, or known short shift in (9), is proved by this construction. Thus the one-colour deletion is not an authorized coverage reduction here. This is the exact failure of this attempted transport, not a claim that a different arithmetic argument cannot bound it.

## 4. A fully safe all-start overcover is paid and larger

For completeness, one can permit every normalized target R_h at every start d_g^-1. This contains all matched original comparisons (7), so coverage is retained. On the nonsplit side a hit R_h=z^i/d_g forces equality of norms. If h has group (a_h,tau_h), this gives the ORIGINAL scalar condition

    beta^[2K']=1,
    K'=N+delta'_(h,g)-Hi,
    delta'_(h,g)=ell_h+a_g+H(tau_g-tau_h)/2.    (10)

All exponents are integers and |delta'|<4H for continuing large k. A proper norm gcd factors; a saturated norm leaf gives (10) at the field side, so gcd(beta^(2K')-1,N) is nontrivial. If saturated, odd orders give beta^K'=1 at both sides. The global coprime-order bound exceeds 256k⁴, while |K'-(N-P-Q+1)|<4k⁴ for i<L and the source size bounds. Thus K'=N-P-Q+1 and the checked sum decoder uses P+Q=1+Hi-delta'. This proves recovery for the new overcover rather than silently inheriting an original row label.

But there are up to J times the number of groups different acquired delta' labels, bounded by O(k²), with no smaller native set bound proved here. Enumerating and exact integer dedup costs soft k²; alternatively their bounded support interval has length O(H)=O(k²). Acquiring the corresponding scalar polynomial and applying the old length-L query therefore costs at most soft k², not soft k. This actually initialized safe overcover is worse than retaining the original family. Merely storing starts and targets separately does not charge their terminal contraction.

## 5. Safe quarter powers after a paid odd projection

There is a supporting simplification that does not lower J or L. Set

    W_odd=W^(2^ceil(log2(N+1))).

This costs polylog N. Every local split or field norm-one order divides p-1 or p+1, both at most N+1, so this power kills its entire 2-primary part. It need not preserve a large torus order, and none is required. Native coverage survives any common powering of W; this need not preserve the ORIGINAL W family's entire zero mask. The seed norm is still beta^(2H), so the field-side exclusion proof survives unchanged. Rerun the actual soft-k factor-or-unit seed screen for the NEW W_odd seed: its old split-side unit certificate is not inherited.

Use W_odd in (1). Both E_j and Texp_j=ell_j+chi(j)(N+a_j) are divisible by FOUR. The native even-k argument gives 4|E_j; when chi=-1, Texp=E_j-2(N+a_j), and N+a_j is even. Also 4|H. All local component values of beta W_odd and beta/W_odd have odd orders. Therefore define

    Vquarter_j=beta^(E_j/4) W_odd^(Texp_j/4),
    zquarter=(beta W_odd)^(H/4).

These fourth powers are the unquartered W_odd targets/seed; the support comparison below is with that W_odd family. For any local component, X^4-Y^4=(X-Y)(X+Y)(X²+Y²), and the last two factors are units for odd-order X/Y: a zero would require an element of order 2 or 4. Thus the quarter family has EXACTLY the same norm zero support, including on restrictions. This does not discard nonunit squares. Its norms give beta^(E_j/2) and beta^(H/2), so the same nonsplit-side consumer recovers the original beta condition; beta odd removes the harmless power of two. For the NEW quarter seed, rerun the actual soft-k factor-or-unit screen as well. Its field-side exclusion follows from the actually guarded beta^H order, since squaring does not change odd orders; a split-side collision returns a proper factor. Neither replacement inherits an old seed unit certificate without this paid rerun.

This is a paid, safe refinement for the new quadratic source. It is only constant exponent compression. The horizon I, row count, acquisition ledger and asymptotic query cost remain unchanged; no new endpoint gain is claimed from the older quarter-power idea.

## 6. Common order four does not execute the terminal product by itself

For each supplied row, its scalar norm sequence is

    h_j(i)=Norm(V_j)+Norm(z)^i
               -bar(V_j) z^i-V_j bar(z)^i.

The acquired common characteristic polynomial is

    (T-1)(T-Norm(z))(T²-Tr(z)T+Norm(z)).

The independent source review already proves this, including coincident spectral values. The actual whole-row value at i also has a cheap factorized representation:

    product_j h_j(i)=F(z^i)*bar(F)(bar(z)^i),
    F(X)=product_j(X-V_j).                      (11)

Writing its spectral coefficient array gives the outer product of the J+1 coefficients of F and bar(F), indexed by z^r bar(z)^s, 0<=r,s<=J. One need not expand that O(J²) array: the factorized state (11) costs soft J. But taking the interval product of (11) is precisely Norm(product_i F(z^i)), the terminal query already being investigated. Constant-order ROW recurrence has not provided a closed constant-order INTERVAL-PRODUCT update. This identifies the state returned by this tested fusion; it is not a lower bound against another scalar contraction algorithm.

## Complete ledger and scope

All source discovery/preparation, all rows, all S_j/P_g, pair centers/starts, and an optional odd projection cost soft k. The acquired antipodal group degrees total J/2; the common-seed reconstruction has degree J. Complete query plus original-leaf recovery remains soft(J+sqrt(JL))=soft k^(3/2). Independent group queries or the executed all-start scalar overcover have worst-case soft k² ledgers. None is counted as a sixth-rate result.

The concrete positive output here is the full acquired colour/antipode contraction (3)--(5), with exact varying-center starts (6)--(7), an explicitly safe but larger overcover (10), and a quarter mask justified after actual odd projection. The attempted inverse fusion fails to remove those starts or the carry term (9). The remaining objective is a paid contraction across the varying group starts with J=O(k), L=O(k²), preserving the existing norm-leaf consumer; no such faster step has been initialized in this report.
