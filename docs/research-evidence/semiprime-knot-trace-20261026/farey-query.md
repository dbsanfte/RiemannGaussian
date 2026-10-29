# Native Farey triples: exact phase and stationary-sector branch tests

26 October 2026. Scratch, bounded paper calculation; no experiments or repository edits. Consulted the old `skein-selector.md` and the archived supplied-interval `factorlab/experiments/farey_cover.py`; the latter is pinned at `/tmp/semiprime-arithmetic-locator-20261024/sources/farey_cover.py` and was also checked by the integrating parent. The old width-two trace and pair-first consumer are prior credit. **No new guaranteed branch selector or faster whole query is established.** The new calculation tests an actual determinant-one native triple, not just existence of trace recurrences.

## 1. Known inputs and what an acceptable branch must retain

For each native row v=(a,b), lambda is an actual uncentered root in [0,H), H=k², of lambda²=4abN mod H. Its label is E_v=a+bN+lambda. The same-lambda swapped row has E'_v=b+aN+lambda. An original physical leaf is beta^(E_v-Hi)-1 with the certified signed index and deleted-zero-row metadata. A recursively chosen subtree must retain at least one actual local-hit row, or return a factor; a saturated additive trace zero alone supplies no such certificate.

At the guaranteed stationary row,

    aP-bQ=0 mod k,
    HI=aP+bQ+lambda.

The complete catalogue's original coverage and the existing legal negative-index decoder remain authoritative. No new all-primes claim follows from the sample-free algebraic identities below.

## 2. Execute the common-swap Fricke character

Let A=beta^((N-1)/2) and

    rho_v=beta^((a+b)(N+1)/2+lambda), d_v=a-b.

These are acquired units with short-bit exponents. Exactly,

    beta^E_v=rho_v*A^(-d_v),
    beta^E'_v=rho_v*A^(d_v).

Thus normalized swap traces are t_d=A^d+A^-d, and their split quadratic is

    g_v(Z)=Z²-rho_v*t_(d_v)*Z+rho_v².

For Farey neighbors v,w (det(v,w)=+/-1), d_(v+w)=d_v+d_w and d_(v-w)=d_v-d_w. The actual commuting SL2 matrices diag(A^d,A^-d) therefore obey

    t_(d_v)*t_(d_w)=t_(d_v+d_w)+t_(d_v-d_w).        (1)

Their Fricke cubic t_(d_v)²+t_(d_w)²+t_(d_v+d_w)²-t_(d_v)*t_(d_w)*t_(d_v+d_w)-4 is identically zero for every input. Using that cubic as the branch nonunit test therefore returns a globally zero value independently of native witness location. It is not an original beta annihilator. This executes one concrete branch-scalar candidate and rejects its interpretation, rather than rejecting trace methods generally.

Keeping rho restores the original pair polynomial, but changes the mediant relation. If lambda_3 belongs to v+w, put Delta=lambda_3-lambda_v-lambda_w. Then

    rho_(v+w)=rho_v*rho_w*beta^Delta.              (2)

The scalar beta^Delta is acquired, but it changes the root argument of g; it is not a harmless overall multiplier of that quadratic.

## 3. Exact conic phase defect at determinant-one triples

Write c_j=lambda_j/2 and S=H/4=3^(2e). Each c_j²=a_j*b_j*N mod S. Suppose, for a native triple v,w,v+w, that lambda_3=lambda_v+lambda_w mod H. Reducing modulo S gives

    2*c_v*c_w=N*(a_v*b_w+a_w*b_v) mod S.

Squaring and using the two individual conic equations yields

    N²*(a_v*b_w-a_w*b_v)²=0 mod S.

Since N is invertible modulo S, this requires

    S divides det(v,w)², equivalently (k/2) divides det(v,w).   (3)

For a Farey pair det=+/-1 and k>2, this is impossible. Thus **every admitted determinant-one native mediant triple has a nonintegral LITERAL exponent clock phase defect**: Delta is not divisible by H. Also -2H<Delta<H and Delta!=0. Beta has odd local order greater than 16H, so beta^Delta-1 is a certified unit. Multiplying by a unit beta^Delta does not itself preserve a root comparison at a fixed clock: (2) would need a shift Delta/H, which is not an integer. This only excludes a literal integer-exponent shift Delta/H. It does not exclude a modular alias beta^Delta=q^t modulo a hidden local order, even for some short t; no such alias or its acquisition is proved here.

There are actual retained triples to which this applies for every prepared semiprime once k>910. Put epsilon=1 if N=1 mod3, and epsilon=-1 if N=2 mod3. Take

    v=(1,9*epsilon), w=(9,82*epsilon),
    v+w=(10,91*epsilon).

Their determinant is epsilon and absolute products are 9,738,910<k. The three products abN have even 3-adic valuations (2,2,0), and after removing that power of 3 their units are 1 mod3. Hence all three have square roots modulo S, and actual lambda lifts modulo H. None is an axis or either diagonal; original and swap labels have magnitude greater than the public deletion horizon on the prepared N>256H² branch. This is a native triple, not an independent free-coefficient example. The phase-defect theorem holds for every choice of its actual roots.

The exact number of phase lifts in the first two rows is larger than four because ab has 3-adic valuation two; no four-lift count is used or needed here. The conclusion needs only their existence. Any old diagonal/unit pruning of a particular root must be honored: the algebraic phase statement applies to every surviving triple, without asserting that pruning preserves a specific triple as a witness.

## 4. Stationary-sector test: the relevant adjacency has index k

Let Lambda_(P,Q)={(a,b):aP-bQ=0 mod k}. Since P,Q are units modulo k, this is an index-k sublattice of Z². For any two of its vectors,

    k divides det(v,w).                            (4)

Proof: multiply the determinant by P and replace a_j P by b_j Q modulo k. Since P is a unit, the determinant vanishes modulo k. Thus two Farey neighbors cannot BOTH lie in the stationary lattice. In particular the standard Farey parent-parent-mediant update is not an operation on triples of stationary native witnesses.

More sharply, if v is stationary and det(v,w)=+/-1, the linear form ell(a,b)=aP-bQ takes ell(w) to a unit modulo k. Otherwise a prime dividing k would divide both ell(v),ell(w), contradicting primitivity of ell in the basis (v,w). Hence the fan v+n*w is stationary exactly when n=0 mod k. This is a precise arithmetic constraint on fan traversal, not a claim that a witness cannot occur in a subtree.

For TWO stationary vectors, canonical stationary lambda choices do add modulo H: their integer sums aP+bQ imply lambda_3=lambda_v+lambda_w-H*h for the acquired carry h (0 or1 when both lambdas are canonical). Then I_3=I_v+I_w-h. This is the closure one would need for a witness-preserving sum, but it belongs to the determinant-multiple-k sector, not ordinary Farey adjacency. The carry h is explicit once the correct stationary phases are known. For arbitrary roots in the catalogue they are not automatically those stationary phases.

These calculations leave a specific possible constructive replacement: an index-k/congruence-lattice Farey transfer that selects the correct hidden stationary sector and preserves its phase/index carries. Merely enumerating O(k) sectors or providing a rank-k transfer does not pay the scalar zero predicate. A deterministic branch algorithm still needs a theorem relating its acquired boundary scalar to existence of an original hit in the selected sector/subtree. The ordinary Fricke cubic above lacks that relation.

## 5. Primary literature and actual computational costs

Elzenaar–Martin–Schillewaert, [The combinatorics of Farey words and their traces, GGD20(2026),215–256](https://ems.press/content/serial-article-files/52234), Theorem 4.4, has parity-dependent constant terms in its specific Farey-word trace recursion; For equal generator parameters alpha=beta, Theorem 4.4 gives the common constant 2*(alpha+alpha^-1)^2 (8*cos(theta)^2 for alpha=exp(i*theta)), not generally 8. Only the parabolic constant-8 specialization of Corollary 4.5 is used here; its broader equal-parameter wording must not replace the actual Theorem 4.4 coefficient. The DOI is 10.4171/GGD/832. These polynomials are not simply the native traces t_d. Section 6, especially Eq. (7) and Theorem 6.4, does provide constant two-by-two matrix advancement along an initialized Farey fan, under its stated determinant hypotheses. It gives values at a specified node/fan position, not a witness-selection theorem for our conic arithmetic.

[Chesebro, Farey recursion and the character varieties for 2-bridge knots](https://arxiv.org/abs/1902.01968) supplies character-variety polynomials for specified 2-bridge data. Neither source identifies a trace zero with the native stationary lattice or proves coverage of a recursively selected arithmetic branch. Equation (1) itself follows integrally from Cayley–Hamilton and needs no field hypothesis or source convention.

All displayed scalar data for one triple cost soft O(log N) bits, and all acquired row/rho/phase data cost soft O(J). Known trace/fan indices can be advanced by binary powering, with no division by trace values or collision differences. A nonunit used as a projector/denominator must return a factor or be treated without division; generic character-variety smoothness is not a finite-ring permission. If one actual useful pair were selected with a coverage proof, the prior two-row geometric consumer would cost soft O(sqrt(m)) plus the licensed soft-k recovery. That consumer is not new here.

The prior `farey_cover.py` assumes an externally supplied short interval containing the smaller factor and tests coverage of real critical-point windows. It is an experimental supplied-information interface, not a scalar oracle locating that interval from N. Its floating-point coverage campaign is not evidence for the current exact native selector. No new numerical run was made.

## Outcome

The exact tested branch scalar is either the identically-zero commuting Fricke cubic (no witness localization), or must retain the conic phase factor (2). At actual determinant-one native triples that factor has no literal integer-exponent shift Delta/H, by (3); possible hidden-order modular aliases remain open; the relevant stationary sum closure instead lies in the index-k lattice (4). These statements reject this particular Farey-trace branch construction, not rational tangles, noncommuting representations, conic-specific sector selectors, or newly proved coverage families in general.

A useful next identity must produce a **paid subtree boundary scalar for the hidden index-k stationary sector**, with a proof that an original local-hit row survives each selected branch and with legal signed-leaf recovery. Known-node trace recursion and carry bookkeeping do not supply it. No shorter guaranteed family, initialized whole-query contraction, or factoring exponent improvement is claimed.

## Constructive follow-up: execute the same-color index-k closure

The determinant-one failure above is NOT the final interface. The parent's proposed public color lift repairs it exactly. Let j be a unit modulo H, represented by a chosen lift of a unit class modulo k, and define

    Lambda_j={(a,b):a*j²=b*N mod k},
    L_j(a,b)=-a*j-b*N*j^-1,
    lambda_j(v)=L_j(v)+H*tau_v in [0,H).

Here j^-1 is acquired modulo H, and tau_v is the exact integer canonical-reduction carry. Because

    (a*j+b*N*j^-1)²-4abN=(a*j-b*N*j^-1)²,

membership in Lambda_j makes the right side divisible by k²=H. Thus lambda_j is an actual native conic root. Replacing j by j+k*t leaves its value modulo H unchanged on Lambda_j: the first-order change is -k*t*j^-2*(a*j²-bN), divisible by H, and inverse-expansion higher terms also contain H. This is a rigorous color modulo k, not an H-sized list.

For v,w and v+w in this same lattice,

    h=floor((lambda_j(v)+lambda_j(w))/H) in {0,1},
    lambda_j(v+w)=lambda_j(v)+lambda_j(w)-H*h,
    E_(v+w)=E_v+E_w-H*h.                           (6)

If P=j mod k and v is stationary, the lifted value equals -(aP+bQ) mod H. Thus actual stationary indices satisfy I_(v+w)=I_v+I_w-h. In this sector the parent's repair really does eliminate the nonintegral phase defect.

### Actual acquired character and branch identity

Set public units

    U_j=beta^(1-j), V_j=beta^[N*(1-j^-1)],
    X_v=U_j^a*V_j^b=beta^(E_v-H*tau_v).

Then X_(v+w)=X_v*X_w exactly. The two-by-two diagonal character gives an ordinary integral Fricke relation on this index-k lattice, and the scalar collision factors obey the stronger explicit identity

    B_(v+w)(ZW)=W*B_v(Z)+X_v*B_w(W),
    B_v(Z)=Z-X_v.                                 (7)

No division occurs; all coefficients and carries cost polylog(N) per supplied lattice edge. At the actual coupled indices Z=q^(I_v-tau_v), W=q^(I_w-tau_w), (7) propagates the common-prime zero to v+w. This is a genuine collision-compatible same-color law, unlike applying ordinary Farey neighbors to unrelated conic phases.

However, its exact finite support is a two-index convolution: if parent intervals are [l_v,u_v] and [l_w,u_w] in original I, the child interval is [l_v+l_w-h,u_v+u_w-h]. An original uniform window is not preserved without this expansion. Known-parent zeros imply the child zero at their coupled sum; (7) alone does not say a parent has a hit merely because the child has one, or turn a union-of-subtrees predicate into an intersection test. Conversely a mediant collision need not split into two parent collisions at arbitrary chosen window positions. No backward branch selection is inferred.

### A real coverage-preserving public row subfamily (same exponent scale)

There is a concrete way to acquire short representatives in these colors without querying a Farey subtree. This is an auxiliary construction, not a new query rate. Enumerate O(k) unit classes j modulo k. A basis of Lambda_j is (1,theta),(0,k), where theta=j²*N^-1 mod k. For each public dyadic scale p0 in the prepared smaller-factor range, put q0=N/p0 and Gauss-reduce this basis in the rational weighted norm

    ||(a,b)||_0²=(a*p0)²+(b*q0)².

Exact rational two-dimensional reduction has polylog(N) bit cost per color/scale. The transformed lattice has covolume k*N. Its reduced shortest vector satisfies

    ||v||_0² <= (2/sqrt(3))*k*N,
    |ab| <= k/sqrt(3) < k.

For a nonaxis vector this also forces |a|,|b|<k. An axis shortest vector is (plus or minus k,0) or (0,plus or minus k), the specified native axes. This proves admissibility rather than assuming an arbitrary Farey endpoint lies in the low-product mask.

For the actual color j=P mod k and a dyadic scale with p0/P in [1/2,2], the actual norm is at most twice the guessed norm. Therefore

    |aP+bQ| <= (4/3^(1/4))*sqrt(k*N),
    |I| <= (4/3^(1/4))*sqrt(k*N)/H+1.

A conservative public horizon M'=ceil(4*sqrt(k*N)/H)+2 is O(k^(3/2)) when N<=k⁶. The completely integer implementation may use Dceil=ceil(sqrt(k*N)) and M_int=ceil(4*Dceil/H)+2, exactly the inherited scalar-catalogue horizon. It satisfies M_int<=4*k^(3/2)+4 and 2*M_int+1<=8*k^(3/2)+9<16H for k>16. The following argument uses M_int if this implementation is chosen. There are O(log N) scale guesses and O(k) colors, so all these rows, their true lambda_j values, their opposites, and the same-lambda swapped partners of both orientations cost soft O(k). The swap partner need not lie in Lambda_j; the color character (6),(7) is applied only to the original same-color vectors and their opposites, not automatically to their swaps. This family contains an actual stationary same-index two-prime pair within the stated M' window. Its rows are a subset of the original bounded catalogue, with explicitly chosen roots; duplicates can be merged.

The window constant must be charged: this is a newly proved M' horizon, not permission to assign these rows to a smaller previously fixed prefix. If the inherited horizon already contains M', no enlargement is required. Otherwise this family needs its explicit signed-window ledger and public whole-row zero deletion for M'; the existing small-exponent decoder applies only after those conditions are checked. Already k>16 gives 2M'+1<=8*k^(3/2)+7<16*k²=16H. On that guarded branch, the correct-color short row cannot be a deleted E=Ht with |t|<=M': its local hit gives q^(I-t)=1, so I=t; the integer gap then forces a=bQ, impossible for a nonzero admitted vector with Q>k. The swapped row has the analogous contradiction. Thus public zero-row deletion cannot silently erase the constructed correct pair. A diagonal vector can make the two rows coincide; it is not automatically a nontrivial mixed idempotent. Its same-index global leaf still has the nonzero short gap (P-1)(bQ-a), so the inherited short-annihilator consumer applies if that leaf is found. Center/special-row processing must follow the inherited factor-or-unit routine; no dropped row is restored. Explicitly include the opposites before folding: for lambda>0, opposition changes I to 1-I; for lambda=0 it changes I to -I. Therefore every positive noncenter index is transported into the licensed nonpositive window. The I=0/transported-center case is processed by the paid center factor-or-unit query, not discarded. The M' horizon and this source map must be carried into the final negative-only query.

The virtual weighted-Gauss witness and its content filter d=gcd(|a|,|b|) dividing k are prior work. The new implementation enumerates public colour/scale guesses and selects their canonical stationary roots; it does not claim a new geometry-of-numbers inequality. The old content proof applies to every shortest vector used here because dividing a forbidden content factor preserves this lattice and decreases any positive weighted norm.

This is positive coverage acquisition, but **not a smaller exponent**: it supplies soft O(k) rows of window length O(k^(3/2)). The old joint evaluator on this family costs soft O(k+sqrt(k*M'))=soft O(k^(5/4)). One correctly selected color would need only its logarithmically many scale representatives (or a further known scale selection), and would fit the prior pair consumer; selecting that color or a zero-safe color subtree remains unacquired.

The remaining question is consequently sharper than arbitrary trace existence: can the O(k) public congruence colors, whose exact characters and carry law (6),(7) are paid, be given a fast scalar boundary predicate preserving at least one correct-color short representative? The same-color law is valid and useful input. Its simultaneous knowledge does not yet evaluate a color-subtree norm or provide a safe reverse implication for branch selection. No determinant-one obstruction is applied to this repaired sector.
