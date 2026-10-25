# Parity-repaired native lifts and the exact two-colour canonical phase

24 October 2026. Scratch only. The positive result is a uniform soft-k reconstruction of the CURRENT quadratic-colour family with a public Hensel lift for EVERY tag, canonical quadratic phases and a constant-size carry menu. Its own-row cover, horizon, guards and saturated decoder are proved below. This is an arithmetic normal form, not a faster terminal query. The completed query remains soft k^(3/2).

## Prior work and authoritative source

Read the preserved journal's 2026-10-08 entry beginning near line 29234: it already proves the general exact discriminant identity, full prime-square Hensel phase masks, and a scoped failure of the old explicit Fourier/mask-norm route. Read the distinct balanced a=1/even-B single-clock construction near line 37410. Those Hensel identities, parity techniques and earlier sparse Fourier results are credited; neither the Hensel relation alone nor rewriting a quadratic phase is claimed as new acquisition. Their source-specific nonvanishing/obstruction results are NOT automatically transferred to the changed family here.

The present detail is the parity change a->a+k for THIS acquired quadratic-colour source, unchanged character labels, its proved L'=3H+2 horizon and all canonical carry/consumer margins. Root proposed this repair and canonical phase/filter formulation; this report verifies and initializes it.

Use the paid rough input from rough-torus-working.md SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda` and the actually paid scalar roughening in rough-index-cancellation.md SHA256 `283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0` (independent review `cf9afeef32415820baff4737b43b6f98ef77ca8c05ede1fcb4c87e951ea2b7b5`). All changed base values/rows and the coupled seed were actually recomputed/rescreened there. Both beta and W local orders are k-rough and >C=16H; beta's two orders are coprime and odd, and W is norm one. H=k², N=PQ<=k^6, P<Q, P,Q>16H; k is even and sixth-root scale. B=R[tau]/(tau²-D), R=Z/N, has exactly one unknown nonsplit side. The negative fundamental character chi=chi_D has conductor dividing k and chi(N)=-1.

Put pi=beta W, barpi=beta/W and q=pi^H. The authoritative exponents are

    E_j=N+a_j+ell_j,
    T_j=ell_j+chi(j)(N+a_j), V_j=beta^E_j W^T_j.

Thus chi-plus is PURE pi: V_j=pi^E_j. Chi-minus is pi^ell_j*barpi^(N+a_j). A mixed pi^(N+a)*barpi^ell formula is not used for chi-plus. The actual q and every 1-q^r,1<=r<=C are acquired certified units.

## 1. Execute the parity repair, retaining its true integer changes

For every raw unit tag 1<=j<k acquire the existing integers

    a=[N j^-2]_k, D_j=(N-a j²)/k,
    b_j=center_k(-D_j j^-1), ell=k b_j-2a j.

Center in [-k/2,k/2), and let epsilon_j in{0,1} be b_j modulo two. Define

    a'=a+epsilon_j*k, D'_j=D_j-epsilon_j*j²,
    b'_j=center_k(-D'_j j^-1), ell'=k b'_j-2a' j,
    delta'=a'+ell', E'=N+delta',
    T'=ell'+chi(j)(N+a').                         (1)

Since j is odd and k even,

    b'_j = b_j+epsilon_j*j-k*zeta_j,
    zeta_j in{0,1}, b'_j even,
    ell'=ell-epsilon_j*k*j-H*zeta_j,
    delta'=delta+epsilon_j*k*(1-j)-H*zeta_j.      (2)

For epsilon=0 the wrap is zero. For epsilon=1 the uncentered value is in (-k/2,3k/2), giving exactly those possible wraps; parity is unchanged by subtracting even k. Therefore 1<=a'<2k, with a' a unit modulo H. Every value is public and acquired, at polylog N work per tag. No hidden factor or modular square-root oracle is requested.

The discriminant identity is exact:

    ell'^2-4a'N=H*(b'_j²-4a' c'_j),
    c'_j=(D'_j+j b'_j)/k in Z.                   (3)

It is the already known identity specialized to the actual repaired data, not a new Gaussian cocycle.

## 2. Every tag now has an actual public unit lift

Solve the public congruence

    a' t = -b'_j/2 modulo k/2,

using its unit inverse, and choose 0<=t<k/2. This is equivalent to 2a't=-b'_j modulo k. Put

    Jtilde=j+k t, u=Jtilde^-1 modulo H,
    1<=Jtilde<H/2, 1<=u<H.                       (4)

Both inversions are in public integer residue rings, not hidden local multiplicative groups. The centered lift condition gives

    ell'=-2a'Jtilde modulo H,
    a'Jtilde²=N modulo H.                        (5)

For the second, expand a'(j+kt)² and use D'_j=-j b'_j modulo k. Hence

    a'= [N u²]_H,
    E' = N(u-1)² modulo H,
    chi-minus: T' = -N(u+1)² modulo H.            (6)

The first is an equality of canonical residues because 0<a'<2k<H. The colour is chi(j)=chi(u), since the character is quadratic and its conductor divides k. None of this says that powering by u or Jtilde is injective in a hidden order: these integers may be as large as H and can have prime factors above k. Only public modular inversion was performed.

### Exact correlated filter and its count

All units u modulo H with 1<=[Nu²]_H<2k are precisely TWO representatives per raw tag j. Indeed set j=[u^-1]_k, J=[u^-1]_H=j+kt. Its canonical a(u) must be a or a+k. Equation a(u)J²=N modulo H forces the corresponding centered b' even, and exactly ONE of those two a choices has even b' by (2). The equation 2a't=-b' has exactly two solutions modulo k, differing by k/2. They give Jtilde and Jtilde+H/2. Selecting [u^-1]_H<H/2 chooses exactly (4). Thus the full low-a filter has 2phi(k) elements and the selected set has exactly phi(k), with every original tag represented once.

The paired representatives u and u+H/2 have the same a and canonical phase pair: H is divisible by four, so adding H/2 changes each relevant square by a multiple of H. They also give the SAME j modulo k, hence the same actual repaired b', ell', E', T', colour and integer carries. One may therefore use the FULL low-a filter without the half-inverse selector: enumerating its two representatives per tag costs soft k and its row/seed product is exactly the SQUARE of the selected-tag product. Prime zero support is unchanged, with both copies mapped to the same original j,i. This is retention or deletion of identical duplicate leaves, not division by a potentially nonunit product. The low-a condition itself is never removed. Selection only avoids duplicate descriptions. The selected restriction is

    u in U(H), [Nu²]_H<2k, [u^-1]_H<H/2,         (7)

with its actual colour and canonical carry labels. A complete Gauss phase sum without this correlated low-a filter is a different input.

## 3. Prove the changed own-row coverage and a common horizon

At the own smaller-prime tag j=P modulo k, the OLD integer index satisfies HI=aP+Q+ell. Since P-j is divisible by k, the repaired index is exactly

    I'=I+epsilon_j*(P-j)/k-zeta_j,
    H I'=a'P+Q+ell'.                            (8)

It is integral. Direct inequalities ensure positivity: ell'>-4.5H, while a'P+Q>=P+Q>32H. For its upper bound, a'<2k, P<=k³ and Q<N/(16H)<=H²/16 give

    I'<(2+1/16)H+1/2 < L'=3H+2.                 (9)

The common horizon L' is public and below4H on the continuing branch. There is no computation of the private integer (P-j)/k in the algorithm; (8) is the exact proof of coverage and of its changed labels.

Both exponent differences are the original identities with a' substituted:

    E'-HI'=(P-1)(Q-a'),
    T'-HI'=(P-1)(Q-a') if chi(j)=+1,
    T'-HI'=-(P+1)(Q+a') if chi(j)=-1.             (10)

The local beta order divides P-1, and the norm-one W order divides P-chi_D(P). Thus the ACTUAL repaired row V'_j=beta^E' W^T' satisfies V'_j=q^I' at the own prime as a whole local-algebra equality. Colour labels have not changed. Both colours must still be retained; no sign for the smaller prime or a guaranteed hit in the pure-pi colour is supplied.

All repaired coordinates are acquired in soft k by actual signed binary powers with O(log N)-bit exponents. We changed neither beta,W,H nor q, so the existing q certificate is for the SAME actual seed. Since L'<C and 2L'<C, needed short geometric guards retain explicit margin. If a representation changes a seed later it must prove or rerun that new guard; the row repair alone does not require an unproved transfer.

## 4. Canonical carries are bounded; raw quadratic carries are not

The direct bounds in (1) give

    -4.5H<delta'<H/2,
    -4.5H<ell'-a'<H/2.

In particular the integer envelope delta' in[-5H,H] is safe, and its actual span is less than5H. Put c0=floor(N/H), r0=N-Hc0, and define CANONICAL phases

    e(u)=[N(u-1)²]_H,
    t(u)=[-N(u+1)²]_H.

For all rows acquire eta_E=floor(E'/H)-c0. It lies in{-5,...,1} and

    E'=H(c0+eta_E)+e(u).

For chi-minus also acquire eta_T=floor(T'/H)+c0. It lies in{-6,...,0} and

    T'=H(-c0+eta_T)+t(u).                        (11)

Let q_beta=beta^H and q_W=W^H. The exact two-colour values are therefore

    chi-plus:
      V'=q^(c0+eta_E)*pi^e(u),
    chi-minus:
      V'=q_beta^(c0+eta_E)*q_W^(-c0+eta_T)
                              *beta^e(u)*W^t(u). (12)

There are seven possible eta_E and at most49 carry pairs in the second line. All phase/carry labels, fixed unit normalizers and actual powers are acquired in soft k. This is a truly constant carry menu; it does not assert a short index for u itself, whose public range is H.

By contrast, the RAW N(u-1)² can be of order NH². Its quotient

    kappa(u)=[N(u-1)²-E']/H

is row dependent and can have range of order NH, although its BIT length is still O(log N). Dropping it is not a safe periodicity step. Exactly,

    pi^E'-q^i=q^(-kappa(u))
                  *(pi^[N(u-1)²]-q^[i+kappa(u)]). (13)

The raw chirp moves each row's seed origin by that actual kappa. The raw negative quadratic in the chi-minus W exponent has the analogous distinct quotient. Unit multiplication of an entire difference is lawful; silently changing only its target or its index origin is not. Equation (12), not a raw Gaussian phase with omitted quotients, is the compact canonical normal form proved here.

## 5. All factor/guard/recovery margins remain valid

Norm(V'_j)=beta^(2E'_j) and Norm(q)=beta^(2H), unchanged in form. Distinct repaired deltas have unit-separated norm labels: their differences have absolute value <5H, so |2(delta'_j-delta'_h)|<10H<C, below each beta order. The old derivative/MPE factor-or-target-separation lemma therefore applies after actual coordinate dedup. Saturated difference norms force equal deltas at the nonsplit side; equal unit norms then make a split-side component equality whole, contradicting a distinct global pair. All such preparation still costs soft k.

For the controlled public k, delta' has the SAME congruence modulo k as the old delta. Its exact-delta fibers are consequently still bounded by16. Exact target dedup cannot remove an entire distinct-delta fiber. Thus the repaired full family still has J=Theta(k); no degree shrink is inferred from the lift.

For a nonunit ORIGINAL repaired leaf Norm(V'_j-q^i), i<L', a proper gcd factors. Saturation implies whole equality at the unique nonsplit side, so

    G_beta=beta^(2E')-beta^(2Hi)

has nontrivial gcd. Proper factors; saturation and odd beta orders give beta^(E'-Hi)=1 at BOTH primes. Let their coprime orders be d_P,d_Q>C and D_order=d_P*d_Q>C²=256H². Both E'-Hi and lambda=(P-1)(Q-1) are divisible by D_order. Set Rsum=1+Hi-delta'. Then

    D_order divides Rsum-(P+Q),
    |Rsum-(P+Q)|<4H²<D_order.                    (14)

Here i<3H+2, |delta'|<=5H, P<=k³ and Q<H²/16 give the displayed strict bound for continuing k>16. It follows that Rsum=P+Q; verify the integer quadratic and factor N. The small quantity is this DIFFERENCE FROM THE FACTOR SUM, not |E'-Hi|: E' still contains N. No original old-delta label is reused, and an arbitrary auxiliary chirp sum is not passed to this consumer.

Restrictions retain actual repaired j,i labels. Products use monic arithmetic and known units only; nonunit norms are localized to an original repaired leaf before (14). The longer L' is still within every stated order/decoder margin.

## 6. Executed compression attempt and remaining paired phase

The lift does license exact small-content cancellation on the rough branch. For chi-plus,

    gcd(E',H)=gcd(u-1,k)²=gcd(j-1,k)².

For chi-minus the COMMON scalar/angular content is exactly

    gcd(E',T',H)=4.                              (15)

Indeed the canonical congruences give the gcd of (u-1)²,(u+1)² with H; odd primes cannot divide both neighbours, and for odd u their common squared 2-part is exactly4. These are exact integer gcd statements, not hidden-order information.

For g_j=gcd(E',T',H), acquire

    Z_j=beta^(E'/g_j)*W^(T'/g_j),
    q_g=(beta W)^(H/g_j).

Every prime divisor of g_j is <=k. Thus the original and normalized differences have identical component zero support by rough-group power injectivity, including at ratio one where the geometric quotient is the unit integer g_j. Also q_g^g_j=q exactly, so its short unit differences are certified by the same q guard. No hidden root extraction is used. The index i and its horizon L' are UNCHANGED.

With the controlled k, H has only constantly many divisor types (at most153), so grouping by g_j gives a fully initialized family of constantly many common seeds. All normalized targets and polynomials cost soft k. Completing every grouped query by the actual blocked algorithm costs

    soft(sum_g(J_g+sqrt(J_g L')))=soft k^(3/2).

The chi-minus half of the raw tags all have g=4, and bounded delta fibers leave Theta(k) actual targets in that branch after deduplication. This is a ledger for this executed normalization, not a lower bound on another paired contraction. The universal quarter simplification was already known and is not counted as a new terminal gain.

Finally (12) gives the exact chirp candidate still to contract: selected units u obey the CORRELATED filter (7), their colour is chi(u), and their two canonical phases and constant carry labels are supplied. Per colour/carry group, the actual root polynomial can be formed in soft k from those values; testing it against the common q index interval gives the same old completion. Replacing this selected product by a COMPLETE Gauss sum/image would discard that actual filter, and replacing pi by an H-periodic root would set q=1 despite its certified large order. Neither is done here. The earlier journal's Fourier-mask failure is credited but is not asserted as a theorem about this repaired family.

The proved advance in this pass is the parity-repaired, uniformly lifted two-colour normal form WITH native coverage, exact filter/cardinality and every guard/decoder margin paid. No genuinely faster Gaussian/chirp product or smaller guaranteed index family has been acquired. Whole-query soft k and the factoring exponent remain open; no finite family campaign, shared-document edit, generic lower bound or unproved Cayley/Gauss cocycle is used.
