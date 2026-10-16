# Circuit common-factor extraction: uniform acquisition is still unpaid

2026-10-16. Focused primary-source audit and exact differential identities for the direct collision locator. No nearlinear locator algorithm or actual-source lower bound is proved.

The current input is stronger than an ordinary black box: a paid formal straight-line program of size s=soft O(m) returns all B=Theta(m) channel values N_r(X) at one arbitrary scalar X. Channel degree d=O(m), and their squarefree field-side gcd H_hit has degree h=o(m) on the retained family. All circuit setup and fixed unit constants are paid. The desired NEW operation is uniform extraction of H_hit, or a factor-selective consequence, in soft O(s+d) total work. Its existence as a short circuit is insufficient; for a univariate degree-h polynomial, a Horner circuit of size O(h) exists trivially once its h+1 coefficients are admitted as constants.

The previously audited Kaltofen--Trager evaluation-box algorithm, Huang--Gao sparse gcd, safe-center content and rare target probes are not presented as new results here.

## 1. White-box SLP closure does not supply a nearlinear constructor

Kaltofen, Single-Factor Hensel Lifting and its Application to the Straight-Line Complexity of Certain Polynomials (STOC1987), primary author PDF https://kaltofen.math.ncsu.edu/bibliography/87/Ka87_stoc.pdf . Inspected the introduction, single-factor lifting and Theorem4. For division-free input SLP length ell and gcd degree h, that theorem gives an output SLP length

 O(ell*M(h^3)+h^2*M(h^2))

under its large-field hypothesis. This is genuinely sensitive to OUTPUT degree, unlike a bound stated only in input degree. But the introduction explicitly distinguishes these short output programs from uniform polynomial-time construction: scalar/seed acquisition is not provided by that degree-independent length theorem. Its proof uses specialization and single-factor Hensel data. In our univariate setting, the specialized seed gcd is already a univariate common-factor problem; it is not supplied by the channel evaluator. Even an h=polylog(m) circuit-length conclusion would not acquire those constants. The actual proven h=o(m) promise is weaker still and does not make the displayed polynomial h factors polylogarithmic.

Kaltofen, Greatest Common Divisors of Polynomials Given by Straight-Line Programs (JACM1988), primary PDF https://kaltofen.math.ncsu.edu/bibliography/88/Ka88_jacm.pdf . Inspected the model and algorithmic guarantees. This gives randomized program transformations polynomial in input length AND unary input degrees (and the relevant failure/bit parameters). It is a uniform SLP result, not merely the older evaluation-box interface, but it does not assert a soft O(s+d), or soft O(s+h), transformation for our channel family. Its general polynomial-time closure cannot be read as nearlinear arithmetic acquisition. Applying field algorithms over Z/N also needs factor-aware inversion/branch contracts; hidden local fields are not supplied.

## 2. Directed evaluation handles splitting overhead, with a multiplicative dimension cost

Van der Hoeven--Lecerf, Directed Evaluation, final version October2020, primary https://www.texmacs.org/joris/direval/direval.pdf . Inspected its specification and Theorem4.2. For an explicitly separable algebra K[x]/mu of degree d, a computation tree of detailed costs tau_in,tau_out,tau_add,tau_mul,tau_div has panoramic evaluation bound

 O((tau_add*d+(tau_out+tau_mul)*M(d)
       +(tau_in+tau_div)*M(d)*log d)*log d).

This is a valuable theorem controlling shared branching and preventing wasteful recomputation. It is NOT additive in circuit length and algebra dimension. Evaluating the s~m channel circuit at a generic root of D_B, with d~m, costs about soft O(s*d) under this theorem; returning B~m algebra elements also incurs tau_out*M(d). The known small hit factor degree h does not replace the initial degree d in the theorem's input. A structured early-splitting implementation could conceivably do better, but it needs a new charged analysis using the actual circuit; no such theorem was found here. The base field, separability/Bézout data and inversions are explicit prerequisites, not automatic composite-ring operations.

## 3. Recent shallow-circuit gcd results have different inputs/work guarantees

Constant-depth circuits for polynomial GCD over any characteristic, arXiv:2506.23220, https://arxiv.org/abs/2506.23220 . Inspected the primary model and Theorem1.1. Over sufficiently large fields, it computes gcd piecewise using constant-depth, polynomial-size ratio circuits. The input is the coefficient vectors of the two degree-n polynomials; the algorithmic interpretation uses polynomially many processors and constant rounds, with field zero tests. It does not take our unevaluated vector SLP and produce the locator in nearlinear total work. Composing a coefficient-vector gcd circuit with a dense coefficient-extraction circuit does not remove the latter's acquisition cost.

Andrews--Kumar--Rai, Modular Composition & Polynomial GCD in the Border of Small, Shallow Circuits, ECCC TR25-171, January2026 revision: https://eccc.weizmann.ac.il/report/2025/171/ . The PRIMARY REVISION NOTICE reports a gap in Theorems6.2 and6.4 and says the paper's results crucially depend on them. Consequently its advertised nearlinear border-circuit bounds are NOT used as established results. Independently of that issue, the advertised model uses coefficient vectors, infinite fields, division gates and border computation, rather than an exact composite-ring channel-SLP constructor. Saved primary page/text records the notice; no invalid bound is imported.

## 4. A recent cofactor-free Hensel theorem still requires the seed and a different ring

Wang--Ding--Yang--Huang, Explicit Factorization of X^n-1 over Z_(p^e) via Cofactor-Free Single-Seed Hensel Lifting, arXiv:2606.20633, https://arxiv.org/abs/2606.20633 . Inspected the primary setup and algorithm interfaces. It addresses a supplied prime-power modulus, a root-of-unity polynomial X^n-1 with n prime to p, and acquisition/lifting of a seed factor over F_p using that specific cyclotomic structure. Its cached inverse avoids carrying a global cofactor during subsequent lifts. It is not a theorem extracting a common factor of arbitrary circuit outputs over an unfactored squarefree semiprime. The prime p, seed and root-order/coset data are not available for free in the present input. No proof/benchmark claim from this preprint is needed for our mathematics; its stated input alone does not instantiate the desired extractor.

## 5. Differential/Wronskian identities preserve the acquisition gap

There is an exact check for a tempting differential shortcut. In either hidden field write N_r=H_hit*A_r. For any r,s,

 N_r' N_s-N_r N_s'=H_hit^2*(A_r' A_s-A_r A_s').

Thus polynomial Wronskians contain the hit factor squared; constructing/evaluating them is paid by formal AD and circuit arithmetic. This identity is useful but does not extract their common polynomial factor or divide by it. Conversely the projective ratio and its derivatives satisfy

 N_r/N_s=A_r/A_s,
 (N_r/N_s)'=(A_r/A_s)',

as rational identities. Normalizing by a channel and using only these ratios removes precisely the common factor from the rational expression. Thus a proposed ratio/Wronskian NORMALIZATION cannot claim that its pole support automatically equals the hit locator. At a common hit, a logarithmic derivative N_r'/N_r instead contains H_hit'/H_hit plus the cofactor contribution; separating those contributions is another common-factor problem.

These are identities on the actual locator factorization, not a claimed actual pair-of-inputs lower bound. Extra known degree, normalization or source constraints could in principle recover information lost by projective normalization. No claim is made that all differential or homotopy algorithms fail, that every needed precision is Omega(m), or that a short circuit cannot encode H_hit. The missing cost remains uniform factor/seed/coefficient acquisition, not differentiation itself.

## Outcome and next positive contract

No checked primary theorem acquires the locator in soft O(s+d) from this paid vector SLP, nor supplies an output-sensitive bound that fits the actual h=o(m) promise with constants/setup included. The useful target is a UNIFORM structured extractor: it may output a short locator circuit, explicit coefficients, or a factor-selective consequence, but must charge its seed, circuit constants, polynomial/jet precision, oracle/circuit replays and composite-ring branches. A theorem accepting already acquired factor coefficients or a specialized seed does not satisfy that contract. This is a precise applicability finding, not a generic black-box lower bound transferred to the source.

All actually used primary PDFs/texts and the ECCC revision page are adjacent and hashed. No new examples, numerical experiment, repository change, Lean build, improved query bound or full factorization theorem is claimed.
