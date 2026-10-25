# Independent normalized character acquisition review

2026-10-24. **PASS** for the corrected final bytes. No required fixes remain. Scratch review only; no source/repository edits or examples.

Reviewed source: `/tmp/semiprime-native-character-20261024/character-acquisition.md`

Exact SHA256: `83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7`

The earlier 17abce... draft needed one Frobenius-scope clarification in section 5. Its group-ring identity was algebraically correct, but P-rho_j does not annihilate the raw Gauss u without accounting for the additive-root phase. The final source correctly applies it to the zero-grade intermediate u^(Q-a_j*rho_j) and explicitly retains the raw auxiliary phase. The author made that correction; this reviewer did not edit the source.

## Native source, packed rows and even phase

The conductor-first size choice and actual unit-tag construction are consistent with the separately reviewed composite row contract. All inverse tags are units modulo composite k; no field structure or two-preimage bound is used. The native tangent identity and the interval bound require only the actual unit tag and centered integer coefficients.

Both packed forms (1),(2) are exact. In particular rho_s(u^N)=g_s^N=rho_s(C_N)g_r and g_s=u^s/C_s give the alternate single inverse-tag normalization. Every requested full vector is charged soft k. Shared C_N/U or an automorphism descriptor is not counted as an all-row vector list.

D=e0+e1*ell*X^(k/2) has the correct even-order inverse-character phase, retained on nonprimitive components. Unit automorphisms fix it. The supplied inverse and C_j*bar(C_j)=D^(j-1), U*bar(U)=D^k identities give legal actual inverses. T_j(1)=q_G(1)=1 is correct, so full cyclic difference norms are identically zero and are rightly rejected as detectors. Removing e0 is not itself an order or recovery theorem.

Native antipodal carries give T_j*T_-j=q_G^tau D^(N+a), while T_j*bar(T_j)=D^(N+a+ell_j). The shared three-vector family and scalar parameters are genuinely acquired in soft k; all N+a exponents are even so the epsilon phase drops there. These are unit target products, not products of target-minus-seed differences.

## Root-free norm-one normalization and own witness

E_j and H are even, so D^-E_j/2 and D^-H/2 are explicit integer powers. The report does not extract a square root. Their conjugation norms prove R_j*bar(R_j)=Q0*bar(Q0)=1 and R_j R_-j=Q0^tau with the displayed signs and exponents.

At the own tag K=E_j-HI=(P-1)(Q-a_j). Both Q and a_j are odd, so K/2 is an integer MULTIPLE of P-1. D^(P-1)=1 modulo P follows from scalar Fermat for ell and epsilon^2=1, with P odd. Thus the normalizer preserves the own hit. This step does not need a Gauss-base order certificate.

The paired-difference polynomial retains the actual mixed sum S_j. Its first unknown coefficient is not supplied by the common constant center. One row/pair costs soft k, while all expanded rows currently cost soft(k*|G|); this is an actual operation ledger, not an output-size lower bound. Primitive norm evaluation of one supplied vector does not acquire those inputs.

## Beta-coupled paired ideal and recovery

The scalar beta0 multiplier in V_j gives exactly V_j bar(V_j)=beta0^(2E_j), and likewise for q_V. For f=V_j-q_V^i, the identity

    G_beta=bar(V_j)f+q_V^i bar(f)

is correct. Conversely bar(f)=(q_V^i)^-1(G_beta-bar(V_j)f), so (f,bar(f))=(f,G_beta). The only reverse-ideal division is by a known unit.

A CONJUGATE-PAIRED local character equality therefore forces the scalar beta0^(2(E_j-Hi))=1. Odd local beta0 orders remove the factor two, giving an ORIGINAL scalar leaf. A proper scalar gcd factors; a saturated bounded original leaf has its original sum decoder. A single primitive-component zero or a saturated primitive norm does not supply that paired condition, and the source explicitly refuses to decode it automatically. The norm-one R alternative avoids this particular pairing issue but has no original-beta order/decoder bridge. The two normalizations are not conflated.

Augmentation and conjugation-norm scalar projections are actually acquired in soft k and return the old original scalar row family. Their long geometric query is still paid at soft(J+sqrt(JL)); no globally zero augmentation of the raw T difference is promoted to a useful scalar query.

## Correct group-ring/Frobenius scope

Expanding rho_s(P-rho_j)(Q-a_j rho_j) gives N rho_s+a_j rho_j-(a_jP+Q), exactly Lambda_j-HI. At the own tag, Q-a_j*j=0 modulo k, so the intermediate u^(Q-a_j rho_j) is additive-invariant. Its P-Frobenius is therefore rho_j, and the first factor annihilates THAT intermediate. The final paragraph states precisely this and does not claim that P-rho_j kills raw u. Private P,Q remain proof variables rather than acquired group-ring coefficients. Unit-word cocycle identities remain globally valid identities, not selectors for differences.

## Single-C_j rewrite and actual streamed time

Applying rho_s to u^j=C_j g_j gives g_s^j=rho_s(C_j)u. Together with g_j=u^j/C_j, this proves

    T_j^j=q_G^c_j rho_s(C_j)^N C_j^(-a_j*j),
    H*c_j=N-a_j*j^2+k*b_j*j.

The transformed difference (13) has the right sign j*i-c_j. Its exponent is actually acquired with O(log N) bits; the original bounded seed label i is not replaced by that potentially large transformed exponent. No division by j in an unknown group occurs.

The prefix recurrence C_(e+1)=C_e*c_(e,1), including corrected trivial/nonunit-index projectors, initializes an actual streaming algorithm. The e-dependent histogram has ell-2 terms and its own slope. Computing k such histograms/cyclic updates really costs soft k^2. At each unit tag the row powers and permutation cost soft k as well. Accumulating one primitive-component product and taking its orbit norm uses soft-k live vector storage, not k^2 output coefficients, but it does not remove that actual time charge. The report clearly charges this even for ONE supplied i; the long interval remains additional.

## Powered paired hit: full rough preparation is essential and paid

The source correctly distinguishes j being a unit modulo k from being coprime to local beta0 orders. Its stronger powered bridge first invokes the OLD both-local-order cleaning: use a fully factored exponent containing all small-prime powers, resolve a global kernel by the outside-product tree, and run the order/q screens. The preserved rough-order-cleaning report was independently read during this audit. Its one-base bit cost is soft k, it handles saturated collapse without a too-long short-annihilator call, and its final orders are both k-rough and >16k^2.

Hence every prime factor of 2j is <=k while every retained order prime exceeds k, so gcd(2j,ord_p(beta0))=1. A conjugate-PAIRED equality of the jth powers forces beta0^[2j(E_j-Hi)]=1 and then the original beta0 equality. The canonical source and decoder margins are restored for this acquired cleaned beta0. The report does not assign this argument to raw Gauss-component orders or plain norm zeros of (13).

## Verdict and scope

All source identities, own-hit preservation, paired recovery, exceptional-character phases, full-current-base guards and streamed costs check. The final source explicitly retains the unpaired primitive-norm recovery gap and the missing soft-k all-row mixed difference query. No original decoder, order certificate, free vector family or new factoring exponent is inferred from a unit aggregate. PASS for these exact bytes.
