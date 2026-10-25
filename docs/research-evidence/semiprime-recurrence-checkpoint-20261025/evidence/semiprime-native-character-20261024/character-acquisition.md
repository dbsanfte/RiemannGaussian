# Native character modulus ell-1: actual normalized differences and acquisition ledger

24 October 2026. Scratch only; no repository edits or examples. Choosing the row modulus AFTER the public auxiliary prime closes the old prescribed-progression supply issue. This report executes the resulting even-modulus Gauss rows, their shared aggregate, and a normalization of ACTUAL differences. It obtains an explicit original-beta recovery bridge for paired differences, but no soft-k all-row/long-index acquisition. The common reciprocal-center normalization and the beta-coupled recovery normalization are tested separately and not conflated.

## Prior work and changed public modulus

Read the packed Gauss construction and native phase cancellation in journal 32100–32260, the preserved character-aggregate reports gauss-cocycle-extraction.md and gauss-weighted-norm.md, and /tmp/semiprime-gauss-period-20261024/period-constructor.md. The old weighted products, packed C_E primitive, global cocycle commutators, and “unit aggregate is not a product of differences” boundary are credited. No growing-character theorem or Stickelberger ideal formula is treated as a hidden-prime phase oracle.

Choose a public prime ell in a paid dyadic interval above ceil(N^(1/6))+1, and PUT k=ell-1. Then k is even, k=Theta(N^(1/6)), and N<=k^6. A sieve finds ell in soft k; there is no remaining requirement to find a small prime ell=1 modulo a PREASSIGNED growing row modulus. Check gcd(N,ell*k); a proper gcd factors. On the prepared hard branch P,Q>16k², these are units automatically. Primitive-root/log-table preparation modulo the known prime ell has the already paid soft-ell cost; factoring ell-1 is public integer work.

Use all tags j in G=(Z/kZ)^*, represented in [1,k-1]. Enumerating them, inverses and the actual native data costs soft k:

    a_j=[N j^-2]_k, D_j=(N-a_j j²)/k,
    b_j=center_k(-j^-1 D_j), ell_j=k b_j-2a_jj,
    delta_j=a_j+ell_j, E_j=N+delta_j, H=k².

Here ell_j is a row exponent, distinct from the auxiliary prime ell. A fixed centered convention handles the even-modulus tie. Because k is even, j,a_j,N are odd and ell_j is even, so EVERY E_j and H is even.

The own tag j=P modulo k is a unit. The same tangent-polynomial calculation gives HI=a_jP+Q+ell_j as an integer. The elementary size proof uses only 1<=a_j<k, the centered b bound, P,Q>16k², P<=k³ and Q<k⁴/16; it does not need primality of k. Thus 0<=I<2H+2 is retained. Original scalar beta setup and its bounded decoder can likewise use these actual unit tags and the same scalar order margins; no numerical hidden order is supplied.

## 1. Packed Gauss rows: actual construction of one row

Let A=R[X]/(X^k-1), R=Z/N, and rho_j(X)=X^j. In the proof cyclotomic additive-root extension use the conceptual Gauss sums g_j, g_0=-1, and u=g_1. The acquired packed primitive gives

    u^E=C_E*g_(E mod k), U=u^k=-C_k.

All factors are units with the exceptional/trivial character projectors retained. For supplied polynomial-bit E, a C_E vector costs soft(ell+k)=soft k, with all histograms and cyclic arithmetic paid. One coefficient automorphism costs O(k), not one scalar operation.

Let s=j^-1 modulo k, r=[Ns]_k, and e_j=ell_j+a_jj+r. The actual native congruence makes e_j divisible by k. The grade-zero target and seed are

    T_j=u^ell_j*g_j^a_j*rho_s(C_N)*g_r,
    q_G=u^H=U^k,
    T_j=U^(e_j/k)*C_j^(-a_j)*rho_s(C_N)*C_r^-1.   (1)

This acquires ONE entire T_j in soft k from the packed vectors, with no expanded additive-root carrier. Native Frobenius cancels the unknown character(P modulo ell) phase and gives T_j=q_G^I modulo the own prime. Negative row exponents are legal units.

An alternate cocycle reduction, using u^(Ns)=C_(Ns)g_r and rho_s(u^N)=g_s^N, is

    T_j=U^[(ell_j+a_jj+Ns)/k]*C_j^(-a_j)*C_s^(-N). (2)

Thus one may remove the explicit varying rho_s(C_N) permutation by using inverse-tag residue seeds instead. This is a genuine identity but does NOT acquire all C_s or their N-powers in soft k: the present algorithm still acquires O(|G|) length-k vectors. Unit inverses in these formulas can be explicit: for unit j,

    C_j*bar(C_j)=D^(j-1), U*bar(U)=D^k,

with the acquired D below, so no untested quotient-algebra pivot is needed. Shared C_N,U and a polynomial word do not pay all individual vectors.

## 2. Even-k antipodes and the globally zero augmentation

Put e0=(1/k)sum_(r=0)^(k-1)X^r, e1=1-e0 and epsilon=X^(k/2). For unit tags, j is odd. The full Gauss product, including trivial and nonprimitive characters, is

    g_j*g_-j=D,
    D=e0+e1*ell*epsilon.                           (3)

Indeed on a nontrivial character it is ell*chi(-1)^j=ell*chi(-1), while on the trivial character it is one. D is a unit, fixed by ALL unit automorphisms, with explicit inverse e0+e1*ell^-1*epsilon. This differs from the old ODD character-order formula by its indispensable epsilon phase.

At augmentation X=1, g_j=-1, C_N(1)=1 because N is odd, ell_j is even and a_j is odd. Therefore

    T_j(1)=1, q_G(1)=1 for EVERY j.                (4)

Consequently the full cyclic scalar norm of T_j-q_G^i is IDENTICALLY zero for every j,i, even on a restriction with no useful hit. It is not a detector. This is a computed necessary correction to a raw full-norm proposal, not merely a metadata observation. Remove e0, or work in the primitive component, BEFORE any character-support norm test. The projection is acquired in soft k, but supplies no new order or factor decoder.

The integer centered relation still gives

    ell_j+ell_-j=H*tau_j, tau_j in {-2,-1,0},
    a_-j=a_j.

Hence

    T_j*T_-j=q_G^tau_j*D^(N+a_j),
    T_j*bar(T_j)=D^E_j.                           (5)

All pair products have a SHARED acquired representation: three length-k vectors q_G^tau, plus O(k) scalar parameters and the common e0,e1,epsilon basis. Since N+a_j is even, its epsilon phase disappears. This is soft-k whole-pair acquisition and yields the full unit target product cheaply. It remains the old kind of UNIT aggregate; it has not computed target-minus-seed products.

## 3. First actual difference normalization: common reciprocal centers

The even exponents permit a root-free normalization that would be unavailable with arbitrary parity. Acquire

    R_j=D^(-E_j/2)*T_j,
    Q0=D^(-H/2)*q_G.                              (6)

No square root of ell, D or a group element is extracted. D powers are acquired from its three known idempotent/epsilon coordinates, and all exponents are actual integers. For all rows these NORMALIZER DESCRIPTORS cost soft k; applying them to every expanded row still costs its O(k)-per-row output work.

The normalized elements satisfy exactly

    R_j*bar(R_j)=1, Q0*bar(Q0)=1,
    R_j*R_-j=Q0^tau_j.                            (7)

Own coverage survives. For K_j=E_j-HI=(P-1)(Q-a_j), both Q and a_j are odd, so K_j/2 is a multiple of P-1. D^(P-1)=1 modulo P, since ell is a scalar unit and epsilon²=1. Thus D^(-K_j/2)=1 and (6) preserves R_j=Q0^I at the own prime.

Now execute the product of TWO actual differences at a common known seed z=Q0^i:

    (R_j-z)*(R_-j-z)=z²-S_j*z+Q0^tau_j,
    S_j=R_j+Q0^tau_j/R_j.                         (8)

The leading coefficient and constant term are acquired in common shared form. The mixed sum S_j is the next ACTUAL coefficient needed. Pair products or their Stickelberger/group-ring ideal data do not provide it. One R_j and S_j are computed in soft k by (1),(6); all such S_j currently cost soft(k*|G|) explicit coefficient work.

For each of the three tau groups, taking product of the quadratics in (8) would supply the target-minus-seed polynomial; it asks for the mixed symmetric coefficients of the varying S_j. The fact that their constant terms are common is not that acquisition. Computing its first X coefficient already asks for the corresponding sum of S_j. This is the exact retained term in this common-center contraction attempt, rather than a generic rank objection.

Augmentation of (6) is still one, so primitive/nontrivial projection remains necessary. A primitive orbit-norm routine can acquire the norm of ONE supplied difference in soft k: multiply its explicitly supplied primitive component over the public unit-group automorphisms by binary orbit-product recursion. This operation is proved in the companion literature report. It is zero safe, but it does not supply the differences or all native mixed sums for free. At a fixed seed, acquiring |G| row differences or applying that routine separately already costs soft(k*|G|). The long i interval is additional.

Even norm-one primitive-component hits need a NEW recovery certificate: Q0's character-component orders have no inherited scalar-beta bound, and a saturated primitive norm may involve different components at P and Q. Norm-one conjugation pairs the two corresponding character roots, but does not turn those component orders into the original beta orders. No old scalar decoder is invoked on (8).

## 4. Alternate normalization: preserve an ORIGINAL-beta factor witness

Test a different normalization before stopping. Let beta0 be the original prepared odd-order scalar base, with its certified local/global and H-power margins. Define

    V_j=beta0^E_j*R_j,
    q_V=beta0^H*Q0.                               (9)

All additional scalar powers are acquired for the WHOLE family in soft k; D and beta normalizers remain explicit units. The own hit is preserved because beta0^K_j=1 modulo P. Exactly,

    V_j*bar(V_j)=beta0^(2E_j),
    q_V*bar(q_V)=beta0^(2H).

For an ACTUAL difference f=V_j-q_V^i, put

    G_beta=beta0^(2E_j)-beta0^(2Hi).

There is a division-free identity and ideal equality

    G_beta=bar(V_j)*f+q_V^i*bar(f),
    (f,bar(f))=(f,G_beta).                         (10)

The reverse inclusion uses only the acquired unit (q_V^i)^-1. Thus a genuinely paired character hit forces the ORIGINAL scalar beta0 equality (squaring preserves its odd orders). At a selected bounded original j,i, a proper gcd of G_beta factors; a saturated G_beta is an original bounded scalar leaf and its original decoder applies. This is an actual recovery bridge, not an inherited order claim for q_V.

But the simple primitive norm of f can have UNPAIRED zeros: V_j and q_V^i have different prescribed norms unless G_beta=0. Formula (10) therefore does not turn a single arbitrary component zero of f into a beta witness. Using the norm-one R version avoids that pairing issue but loses the scalar beta recovery bridge. This is a distinction for these tested normalizations, not a universal impossibility statement.

At augmentation, (9) gives beta0^E_j and beta0^H. Its conjugation norm gives beta0^(2E_j) and beta0^(2H). ALL these scalar targets and seeds are acquired in soft k and preserve the original native collision source. They are a concrete sufficient scalar reduction with a legal decoder; however their complete long product is precisely the old degree-|G| original scalar query, with base beta0 or beta0². The entire family at ONE supplied i is tested in soft k by MPE of its acquired target polynomial, and any nonunit is recovered by the original beta controller. This does not test all O(k²) indices at that cost.

The current fully initialized whole-interval completion is still

    soft(J+sqrt(JL)), J<=|G|<=k, L=2k²+2,

including coefficient acquisition, every giant start, restrictions and original-leaf recovery. At the worst native scale it is soft k^(3/2). The proposed Gauss normalization does not shrink its degree or horizon. Padding away the scalar augmentation instead discards this direct decoder and leaves the unresolved mixed primitive query in (8).

## 5. Group-ring difference and global cocycle scope

Writing the actual row operator as Lambda_j=ell_j+a_j*rho_j+N*rho_s, one has at the own index

    Lambda_j-HI=rho_s*(P-rho_j)*(Q-a_j*rho_j).      (11)

The right side expands to N*rho_s+a_j*rho_j-(a_jP+Q), so the signs and the original index are exact. At the unknown own prime, the first factor annihilates the zero-additive-grade intermediate u^(Q-a_j*rho_j), not u itself: Q-a_j*j=0 modulo k makes that intermediate additive-invariant, and its P-Frobenius is rho_j. Full Frobenius on u can include an auxiliary additive-root phase. Thus the exact factorization proves coverage on that intermediate; it does not initialize the private P or Q as group-ring coefficients or acquire a new row.

Taking full known Galois products of UNIT words in (11) can use Hasse–Davenport/cocycle distribution, and includes the old acquired weighted products. Replacing u^Lambda by u^Lambda-z is different: (8) shows the first missing additive coefficient explicitly. Associating the packed cocycle C_(ab)=C_a^b*rho_a(C_b) in different orders is a global equality before reducing at either prime; its zero residual is not a selector. No unknown phase is removed from an ACTUAL difference merely because its ideal factorization or unit product is known.

## 6. Executed single-quotient rewrite and the shared-prefix test

Root supplied a sharper actual rewrite, which can be proved without any unknown C_P or C_Q. Define the acquired integer

    c_j=(N-a_j*j²+k*b_j*j)/k².

The numerator is divisible by k² by the same native centered equation. Apply rho_s to u^j=C_j*g_j to get g_s^j=rho_s(C_j)*u. Also g_j=u^j/C_j. Therefore, with all negative row powers legal,

    T_j^j
      =u^[j*ell_j+a_j*j²+N]*rho_s(C_j)^N*C_j^(-a_j*j)
      =q_G^c_j *rho_s(C_j)^N*C_j^(-a_j*j).         (12)

The exotic row data have genuinely reduced to ONE quotient C_j per tag. Comparing the jth powers asks for the actually acquired packed difference, up to known units,

    f_(j,i)=rho_s(C_j)^N-q_G^(j*i-c_j)*C_j^(a_j*j). (13)

The original bounded i label is retained even though the transformed exponent j*i-c_j need not be small. All such integer exponents have O(log N) bits. No division by j in a group is performed.

Now TEST a shared prefix algorithm rather than count (12) as acquisition. The exact recurrence is

    C_1=1, C_(e+1)=C_e*c_(e,1).

For the known public log table l(t), its actual Jacobi histogram is

    J_(e,1)(X)=sum_(t!=0,1) X^[e*l(t)+l(1-t)] mod (X^k-1).

The corrected multiplier c_(e,1) includes the acquired exceptional-character projectors from the packed primitive. Equivalently all these histograms are the marked evaluations H(X^e,X), where H(S,X)=sum_t S^l(t) X^l(1-t). A different e changes the slope of this SAME public sparse histogram; it is not a coefficient permutation of one fixed histogram in general. The doubling multiplier c_(e,e)=rho_e(c_(1,1)) can be shared as an endomorphism descriptor, but the odd increment still needs the corresponding c_(2e,1). No prefix matrix action or field Fourier theorem supplying their nonlinear native contraction is assumed.

A complete STREAMED algorithm for one fixed known i is nonetheless initialized:

1. Maintain C_e and compute each corrected c_(e,1) by its actual O(ell) histogram and cyclic multiplication. This costs soft k per increment, including nonunit e residues/trivial characters.
2. At each unit e=j acquire (13) from the current C_j by unit powers and the coefficient permutation rho_s. Accumulate the primitive-component product of these actual differences in ONE length-k vector.
3. Apply the companion zero-safe primitive orbit-norm algorithm to that vector, obtaining exactly the scalar product of primitive norms of all (13). The companion report is character-literature.md, SHA-256 24ec2dd1529a9c36070df12e880347c21c8841e7367eaa711c0bd7cfcf601c02.

The resulting actual scalar is computed WITHOUT writing k² row-output coefficients: the live memory is soft k. Its TIME is still soft k², from k acquired histogram/prefix updates, plus the paid soft-k row powers/norm accumulation. This identifies actual operations of this tested completion, not an output-size lower bound. A selected binary C_j call is soft k, but the shared binary tree has O(k) different states/multipliers if all selected j are expanded; no new soft-k simultaneous prefix contraction has been constructed. The subsequent long i interval is additional, and powering by j also changes the seed base to q_G^j.

### Powered-hit recovery is conditional on a PAID original rough base

Raising to j can introduce hits in the Gauss-derived component groups. It is not an equivalence merely because j is a unit MODULO k. There is, however, a safe paired original-beta repair. First use the OLD fully charged smooth-order cleaning on beta0 so BOTH its surviving local orders are k-rough and still above16k², with its factored-kernel and order/q screens handled. This preparation costs soft k or factors N; it is not an extra hypothesis obtained from the Gauss base. The canonical scalar coverage remains valid for the resulting unit beta0.

Use the beta-coupled V_j,q_V of (9) with this beta0. A conjugate-PAIRED equality V_j^j=q_V^(j*i) in a local character component forces

    beta0^[2j*(E_j-H*i)]=1.

Every prime factor of ord_p(beta0) exceeds k, while j<k and that order is odd. Thus gcd(2j,ord_p(beta0))=1, giving the ORIGINAL scalar equality beta0^(E_j-H*i)=1. Proper gcds factor, and a saturated bounded original leaf has the original beta decoder. This proves the selected powered-hit bridge under its actual paid guards.

A plain primitive norm zero in (13) does NOT supply that paired beta-coupled equality; it still may be an unprepared component/power hit. Computing the relevant scalar beta condition directly gives exactly the old scalar source again. The cofactor j has not shortened the bounded original i horizon, and its removal cannot be assumed for raw Gauss-component orders. Hence this single-quotient prefix attempt has a real initialized scalar output at soft k² and a precise conditional recovery bridge, but no soft-k covered long query.

## Acquisition and recovery ledger

| Operation | Paid work | Delivered quantity |
|---|---:|---|
| Public ell, k=ell-1, character/log tables | soft k | supplies old auxiliary progression gap |
| Unit tags/native metadata | soft k | covers own P modulo k |
| Shared C_N,U,D,q_G and projectors | soft k | explicit length-k vectors |
| ONE grade-zero native T_j | soft k | actual packed coefficients |
| ALL T_j by current algorithm | soft(k*|G|) | no soft-k expanded-output claim |
| All pair products / D normalizer descriptors | soft k | shared constant terms, not S_j |
| One normalized primitive difference norm | soft k after input | actual scalar; no inherited saturation decoder |
| Pair difference (8) | soft k per supplied pair | mixed S_j retained |
| Single-C_j prefix scalar at one i | soft k² time, soft k memory | actual primitive norm product; saturation not automatically decoded |
| Beta-coupled scalar row family | soft k | original prepared source / legal witness bridge |
| Complete scalar projected query | soft(J+sqrt(JL)) | actual original factor/witness recovery |

The new public-modulus choice removes the small auxiliary-prime supply gap. Even parity additionally supplies the root-free normalizations (6),(9) and makes their support/recovery trade-offs explicit. Their first actual product-of-differences contraction retains S_j, and their safe scalar projection returns the original long query. No soft-k all-row mixed statistic or primitive long norm with complete recovery has been acquired; no sixth-rate or generic lower-bound claim follows.
