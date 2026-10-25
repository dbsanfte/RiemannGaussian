# Prime-cube modulus supplier for coarse native tags

24 October 2026. Scratch only. The preferred construction is k=2c r³ and m=2c r², with a known public prime r coprime to the negative fundamental conductor c. It is a fully paid replacement for the previous k=2c times prime setup. It supplies k at sixth-root scale, m|k, m>=k^(2/3), and only r<=k^(1/3) original tag lifts per coarse class. All original coverage, roughness, parity, factor-or-separation and good smaller-nonsplit exact-one-minus promises survive. Arbitrary delta fibres need NOT remain constant or polylogarithmic; they are not used to certify separation. No faster coarse readout or whole query is proved here.

## 1. Conductor inputs and exact conditional scope

Let K0=ceil(N^(1/6)), N=PQ with distinct odd P<Q. The conductor labels are the ACTUAL ones from orientation-palette.md, SHA256 97db9cf0004dac3ec2c6c9cc341b27531fb90c51d5f6739e6b121c6bc4e20fbf. They are negative fundamental D with c=|D| and Jacobi(D,N)=-1. Their known factorizations come from one initial D0, with at most one odd prime ell, multiplied by u v, 1<=u,v<=B=bit_length(2N)^33, then fundamental-normalized. Thus every odd conductor prime except possibly ell is <=B. No arbitrary N-sized integer is factored to produce these data.

The source proves c=O(N^(5/32)B²). Its initial small Jacobi-minus D0 uses the already pinned unconditional Burgess/Lau--Wu consequence. Its orientation guarantee uses the explicitly CONDITIONAL QRH least-nonresidue import, with a polylogarithmic list and unrecognized good orientation. Those analytic premises and finite exceptions are preserved verbatim. This note does not prove or silently make that orientation unconditional. The modulus construction below itself is elementary once such conductor data are supplied and the public guards hold.

## 2. Pay for the new scale before invoking any supplier

Set Kmax=125 K0 and M=16 Kmax². If M>=N, use the finite-input trial-division fallback. Otherwise acquire the product of ALL positive integers 1,...,M modulo N using degree-s integer blocks, s=ceil sqrt M, monic MPE at the actual block starts, and an exactly clipped final block. Its cost is soft sqrt M=soft K0 BIT work. Any nonunit block can be descended or scanned in soft s to a term whose gcd is proper: every positive term is <=M<N, so a leaf gcd cannot be N. A NoHit result certifies BOTH primes exceed M.

This screen is run once for the WHOLE new palette, before any torus/scalar routine requiring P,Q>16k². The old smaller threshold is not transferred. All integer labels/exponents have O(log N) bits; the displayed constants do not grow with N. Public guards such as B²<N and the source's bounded Jacobi scan/setup checks retain their finite-input fallback. In particular every later candidate prime dividing a constructed k is below N on the continuing branch.

## 3. Actual public prime acquisition, bounds and factorization

For each conductor c publicly require c<=K0/128. Define T as the least positive integer with 2c T³>=K0; this is an exact integer-root computation. Require T>B. The guard implies s0=(K0/(2c))^(1/3)>=4, and T<=s0+1<=5s0/4.

Sieve through 4T and select primes in the two disjoint Bertrand intervals (T,2T) and (2T,4T). T>=4, so both primes are odd. All conductor primes except possibly the ONE old ell are below T. At most one of these two distinct primes can divide c. Test the known public c and choose a prime r coprime to it. This proves availability for these ACTUAL orientation-label conductors; the two-interval argument is not being asserted for an arbitrary integer c with many unrelated large prime factors. Every primality/factor-avoidance test is paid by the public sieve and known factorization. The cost is soft T<=soft K0, in fact T=O(K0^(1/3)) because c>=1.

Set

    k=2c r³,       m=2c r²,       H=k².             (1)

The exact scale bounds are

    K0<=k<125 K0=Kmax,
    m|k,  k/m=r<=k^(1/3),
    m³=(2c)H,  hence m>=k^(2/3)>=sqrt k.            (2)

Indeed r>T>=s0 gives the lower bound, while r<4T<=5s0 gives the upper bound. All factors of k are explicitly known: the factored conductor, 2 and r³. No factorization of N or of N+1 occurs. The new public divisor m is therefore genuinely acquired, not inferred from a smoothness heuristic.

The guards eventually hold uniformly over the whole old palette. The conductor bound and exponent slack 1/6-5/32=1/96 imply c=o(K0), and T is at least a constant times N^(1/288)/B^(2/3). Thus T>B for sufficiently large N. The finitely many size exceptions, and the analytic orientation exceptions, use the source's explicit whole-algorithm fallback; no numerical threshold or public recognition of the good label is claimed.

For comparison the originally suggested square construction also works for setup: k=2c r²,m=2c r, T=ceil sqrt(K0/(2c)), guards c<=K0/32,T>B, and two Bertrand intervals give K0<=k<25K0 and m>=sqrt k. The cube construction is preferred because the exact extra identity m³=(2c)H supports the separate phase-normalization test. That test and any long-query consequence are not assumed here.

## 4. Rebuild the ACTUAL controllers and native rows

Since the common screen gives P,Q>16Kmax²>16H and k>=K0, we have

    N<=k^6,  P<=sqrt N<=k³,  Q<N/(16H)<=H²/16.

Apply the already proved scalar rough controller and rough torus supplier with THIS k,D. Their hypotheses are N<=k^6, P,Q>16k², D fundamental/Jacobi-minus, c<=k/2 and synchronized conductor data; none requires a new prime of order-k Gauss-character conductor or a cyclic unit group modulo k. Here c|k/2 is literal. The public factors of k are supplied even though r appears cubed.

These paid routines return a proper factor or actual odd k-rough beta and norm-one W with both local orders >16H. The torus supplier's complementary exponent tree, palette/AP escape and factor-or-common-order proof are unchanged for composite k and prime powers. Their budgets are soft k. Rebuild EVERY native a,b, parity repair, row, original label and q=(beta W)^H. Rerun the actual COUPLED q screen through 16H; scalar and torus order guarantees alone do not certify split-coordinate cancellations. Return any verified factor from that screen or continue with its actual unit differences. No old point, base, modulus or q guard is reused unscreened.

The exact native arithmetic is valid for every even k. For each unit tag 1<=j<k acquire a=[N j^-2]_k, D_j=(N-a j²)/k and the centered b congruent to -D_j j^-1 modulo k. Put epsilon=b mod2, A=a+epsilon k and b' the centered representative of b+epsilon j modulo k. Then A is odd/unit, 1<=A<2k; b' is even; and

    ell_j=k b'-2Aj,   -9H/2<ell_j<H/2,
    A(j+kx)²+ell_j(j+kx)+N=k²(Ax²+b'x+c_j)          (3)

for an actual acquired integer c_j. The parity proof uses only that k is even; r³ adds no exception. The signed row exponents still have O(log N) bits and all O(k) rows are acquired in soft k. The character chi_D has conductor c|m, is nonprincipal on the unit tags, and half the unit tags have each sign. The own tag [P]_k is a unit because P,Q exceed all public prime factors of k.

The old same-leaf norm/beta and general nonzero-annihilator consumers retain their actual hypotheses and bounds under this changed scale. Original indices are still in [0,3H+2), with the same repaired A,ell data. A saturated original leaf is never replaced by an unbounded new phase or by an auxiliary polynomial coefficient.

## 5. Prime-power fibre caution and a paid separation replacement

The literal old sixteen-element/polylogarithmic exact-delta bound is NOT inherited. The necessary congruence for a fixed delta is

    (j^-1-1)² = 1+delta N^-1 modulo k.

Although j is a unit, j^-1-1 may be divisible by r. Modulo r³, x²=0 has r solutions (x divisible by r²), and a nonzero square of valuation two can have 2r solutions. Modulo r², x²=0 likewise has r solutions. Therefore these degenerate factors can enlarge delta fibres by a factor O(r). An upper bound of O(r B²), rather than a constant or a bare polylogarithm, follows by combining the usual squarefree conductor roots and the two-adic factor v2(k) in {1,3,4}. Fixed unit-square equations such as j²=-N modulo k still have at most two roots at the odd r³ factor, because their derivative is a unit; these must not be confused with the degenerate shifted square above. In particular old fixed PLUS-collision or bounded-width auxiliary-ideal theorems are not transferred with their old constants.

What is needed for the native query here is factor-or-unit-separation, which has a different softly linear proof independent of fibre width. For each queried canonical colour family separately, express its acquired roots in the public basis (1,tau) with canonical residues modulo N and sort/deduplicate exact GLOBAL coefficient pairs in soft k work, retaining an original row label and its colour per root. Equal roots represent identical query factors up to multiplicity and can be retained once for zero support; the good unique own hit cannot be lost.

For the retained J distinct global roots, acquire F and all F'(V_j) by a product tree and monic MPE, soft J work. If every derivative norm is a unit, all pair differences are unit and separation is certified. Otherwise choose a nonunit derivative and localize one of its factors V_j-V_a by a binary product tree or direct scan, costing soft J extra work for this ONE row. The selected difference is globally nonzero by deduplication. A proper norm gcd factors. If its norm gcd is N, the Jacobi-minus quadratic algebra has one nonsplit field side, where zero norm forces both coordinates zero; since the difference is not globally zero, a coordinate then gives a proper gcd with N. Thus the first nonunit distinct pair already factors. No repeated removal campaign, quadratic fibre scan or pairwise k² input is hidden. A continuing branch has actual unit-separated roots in soft k.

This proves the root preparation required for the query; it does not rebuild the old constant-width norm-fibre ideal at the same width. If a later algorithm needs such an ideal, its now-growing fibre degree must be paid separately.

## 6. Exact-one MINUS proof survives r³

At a good label, P is the smaller nonsplit prime. The odd beta and torus orders divide P-1 and P+1, are coprime, and each exceeds 16H, so their product exceeds 256H². Every minus hit i in the original horizon makes that product divide

    K=A P+Q+ell_j-H i.

The same native bounds (3) and P<=k³,Q<H²/16 give |K|<8H² on the continuing range, so K=0 as an INTEGER. (The promises P>16k² and P<=k³ force k>16.) Multiply by P and use (3) to obtain

    A(P-j)²+k b'(P-j)=0 modulo k².                 (4)

For any prime p dividing k, let e=v_p(k), s=v_p(P-j). If s<e, the first term has valuation 2s, while the second has valuation at least e+s>2s. They cannot sum to a multiple of p^(2e). Hence s>=e at EVERY prime, including e=3 at r. Thus k|(P-j) and j is exactly the own tag [P]_k. This argument does not count square roots of a degenerate quadratic.

Conversely the own-tag expansion (3) gives the integer index I=(A P+Q+ell_j)/H. Its bounds are positive and I<33H/16+1/2<3H+2. For the minus exponents E=N+A+ell_j and T=ell_j-N-A,

    E-HI=(P-1)(Q-A),
    T-HI=-(P+1)(Q+A).

The actual beta and W orders therefore give the own collision. Since chi_D(P)=-1 it belongs to the retained minus family. The actual q unit screen makes all indices in the horizon distinct, so the local hit is unique. The exact-one proof is consequently valid for the cube modulus, without any fixed PLUS-fibre count. Wrong orientations and the split Q side retain the old bounded validation/fallback scope.

## 7. Coarse residue data and honest query cost

Every unit coarse tag s in [1,m) has EXACTLY r original lifts

    j=s+m t, 0<=t<r.

All are units modulo k: conductor and two-adic units are fixed by s modulo m, and r already divides m so none becomes divisible by r. Since c|m, all lifts have the same character colour. Their actual native rows and original metadata are acquired in soft r extra work from the supplied bases, or are selected from the already acquired full menu. A known correct coarse tag therefore leaves at most r<=k^(1/3) original candidates.

This is only a supplier/data theorem. If a future soft-k weak readout identifies the correct coarse tag at the good prime, the existing covered block query on its r candidates costs soft(r+sqrt(rL))<=soft(k^(7/6)), with all original rows and the same decoder. Today the available coarse-label gradient still has degree-J diagonal F and costs soft sqrt(JL)=soft k^(3/2), so that conditional downstream saving does NOT improve the whole clock. Querying every lift separately is not silently charged as one original-row locator. No new success promise is assigned to the phase-normalized family without the separate algebra/guard proof.

## Exact inherited pins and totality

- orientation-palette.md: 97db9cf0004dac3ec2c6c9cc341b27531fb90c51d5f6739e6b121c6bc4e20fbf.
- native-pairing.md: 06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016.
- implicit-evaluation.md: 5600980cbd17a37e09c79ed9503766cd081df9753bf8593443cc66bc0d4c0646.
- rough-torus-working.md: 6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda.
- rough-index-cancellation.md: 283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0.

All O(B²) conductor labels multiply the paid soft-K0 preparation by only polylogarithmic factors. Public guard/setup failure and any unresolved bounded query label invoke the previous whole-algorithm fallback, accepting only verified factors or authoritative original witnesses. Under the same pinned analytic imports, the size and orientation exceptions are finite but need not be publicly recognized in advance. The honest output remains a factor or a prepared unrecognized orientation palette with the stated conditional asymptotic good label, not an unconditional new factoring theorem. No shared/frozen source, numerical example or backend was changed.
