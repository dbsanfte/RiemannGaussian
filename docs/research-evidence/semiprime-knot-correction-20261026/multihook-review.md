# Independent review of multihook-correction.md

26 October 2026. Verdict: the annular/satellite distinction, dimension-leading determinant, and explicit two-hook algebra are correct. **One convention correction is needed to match the acquired ordinary Seifert polynomial:** the quantum parameter in the hook brackets must be a square root of the ordinary Alexander evaluation parameter. No source/repository edits or numerical campaign.

## 1. Annular Giambelli is not multiplicativity of the knot satellite

Checked Lukac, arXiv:math/0110119v1, Theorems 8.1–8.2 (printed pp.15–16): https://arxiv.org/pdf/math/0110119 . The map from symmetric functions to positive annular skein elements is a ring map. Consequently Frobenius Giambelli is an equality of annular patterns. It does not assert that inserting those patterns into an arbitrary fixed knot and evaluating is a scalar algebra map. The report's correlation defects are therefore necessary and well-defined.

The shape lambda_m=((m+1)^m,m) has Durfee rank m, arms/legs m,...,1, size m(m+2), and diagonal hooks 2m+1,...,3. At m=2, the four hooks in its Giambelli determinant are precisely 311,31,211,21, with the signs in (3) correct.

Finite specialization deserves one additional clarification: the color has m(m+2) boxes, potentially beyond the short-order margin, but its maximum hook is only 2m+1. One can use the Jacobi–Trudi/Schur annular presentation with complete functions h_r for r≤2m+1; these require only short quantum-factorial denominators. Thus no inverse of a potentially vanishing [m(m+2)]! is licensed or necessary. Merely invoking a generic large Hecke idempotent without such an integral/localized presentation would not supply this finite-ring justification.

## 2. Quantum-variable correction

For the standard HOMFLY skein with crossing difference z=u−u^(-1), the ordinary Seifert Alexander variable T satisfies

    z=T^(1/2)−T^(−1/2), hence T=u².

Therefore if the dimension brackets are [s]_u=u^s−u^(−s), the one-hook specialization for an acquired ordinary K(T) is K(u^(2s)). With the report's written u=eta, its hook values should be K(eta^(2s)), not K(eta^s). The one-hook scaling rule stated in a HOMFLY variable does not remove this factor of two in passing to ordinary Seifert notation.

To match the requested P_m=∏ K(eta^(2i+1)), set u=s0, with s0²=eta, already explicitly acquired from beta on the native branch, and replace every report bracket by

    [s]=s0^s−s0^(−s).

Keep K_s=K(eta^s). Then all displayed dimension, Gamma_2, and correction identities hold with precisely the desired odd weights. In the Cauchy proof use A_i=eta^alpha_i and B_j=eta^(beta_j+1), rather than native q=eta². Nothing costly is adjoined. All three local orders of s0,eta,q coincide on the odd-order branch, so every unit proof and acquisition conclusion survives unchanged.

Lukac's source uses loop value (v^(-1)−v)/(u−u^(-1)), whereas the report writes (v−v^(-1))/(u−u^(-1)). Declare that its v is the inverse HOMFLY A-variable relative to that source convention (and track corresponding framing convention). This is a harmless convention choice if made consistently; the source's sign cannot simply be copied silently. The explicit dimension formula in the report fixes the algebra used below.

## 3. Leading tau coefficient and units

Work with the corrected quantum u, and tau=v−v^(-1). Since the derivative at v=1 is 2, tau is a valid formal local coordinate over R. In the dimension formula, exactly m zero-content boxes contribute tau. For a hook (a|b), positive and negative nonzero contents cancel the non-diagonal hook factors, leaving exactly

    d_(a|b)=tau*(-1)^b/[a+b+1]+O(tau²).

Applying the **dimension** algebra map to annular Giambelli therefore proves (2). Since

    1/[a+b+1] = u^(a+b+1)/(u^(2a)*u^(2b+2)−1),

its matrix is a Cauchy matrix times unit row/column scales. Cross denominators use positive exponents at most 2m+1; within-arm/leg differences use nonzero exponent gaps below m. The local-order guard proves all factors in the Cauchy determinant are units. Thus kappa_lambda is a unit, and the leading vanishing order is exactly m. This does not acquire its scalar numerical value for free.

The identification [tau^m]W_lambda/kappa_lambda with H_lambda(v=1) requires the report's stated hypothesis that the reduced invariant H_lambda=W_lambda/d_lambda is regular at v=1. Keep that hypothesis attached unless a separate integrality/regularity theorem in the chosen normalization is supplied. Annular Giambelli by itself proves neither arbitrary satellite divisibility nor arbitrary quantum-normalization regularity. In the m=2 discussion, the claimed order of the combined defect follows under precisely this hypothesis for W_332; individual defects need not have that order.

## 4. Exact two-hook correction

The leading dimension signs are +1/[5], −1/[3], −1/[4], +1/[4] for 311,21,31,211 respectively. Hence with A0=1/([5][3]), B0=1/[4]²,

    kappa_332=−A0+B0,
    [4]²−[5][3]=[1]²,
    A0−B0=[1]²/([5][3][4]²).

These signs give exactly the report's Gamma_2 and E_2, with no missing minus sign:

    Gamma_2=(A0 K_5 K_3−B0 K_4²)/(A0−B0),
    E_2=[tau²](B_(311,21)−B_(31,211))/kappa_332.

The identities invert no K_s. Gamma_2 costs O(L) using three scalar evaluations plus known unit brackets. At K_3=0 and K_4 unit, Gamma_2=−K_4²[5][3]/[1]² is a unit. Thus dropping E_2 is not justified as a universal zero-selector substitution; this calculation does not prove a particular unknown native input attains the chosen collision pattern.

The genus-one diagnostic is valid after the quantum-variable repair: for ordinary K(T)=1+c(T+T^(-1)−2), set c=−(eta³+eta^(−3)−2)^(-1). The denominator equals eta^(−3)(eta³−1)² and is a unit under the stated conditions. The difference between traces at eta^4 and eta^3 factors into the two stated differences eta^4−eta^3 and eta^4−eta^(−3), up to units. Therefore K_3=0 and K_4 is a unit. Lifting c to an integer gives a symmetric integer Laurent polynomial with K(1)=1 and an actual genus-one Seifert realization. This is a valid generic-knot diagnostic, not an attained native catalogue/controller construction or a computational experiment.

## 5. Source limitations and scope

Eynard–Kimura, arXiv:1408.0010v2, explicitly studies specified ABJM/supermatrix averages and a torus-knot-motivated deformation: https://arxiv.org/pdf/1408.0010 . Its expectation-level Giambelli structure is stronger than annular Giambelli, but is not a theorem about the arbitrary native Seifert-realized knot or the building block K_s/[s]. The report preserves that distinction.

Mishnyakov–Sleptsov–Tselousov arXiv:2001.10596v4 states tug-the-hook conjecturally: https://arxiv.org/pdf/2001.10596 . The report uses only the elementary invariance of a_i+b_j+1 under the proposed tug, so it imports no conjectural all-knot conclusion. Harper's SIGMA 22 (2026),025 paper is correctly identified as a modified-trace/nonabelian construction with extra data; it does not establish multiplication of these satellite values.

The unweighted determinant rank bound, literal color/matrix output costs, and absence of acquired joint satellite coefficients are scoped correctly. After the quantum-variable repair, this remains an exact correction audit and no new soft O(L+sqrt m) prefix algorithm.
