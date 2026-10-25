# Conditional orientation palette for an exact-one minus collision

24 October2026. Scratch only. This acquires a polylogarithmic list of actual NEGATIVE fundamental discriminants and rebuilt native families. Conditional on the repository's pinned QRH least-nonresidue consequence, one unrecognized label makes the SMALLER prime nonsplit; its canonical minus-only query then has exactly one local collision at that prime. The preparation costs soft-O(N^(1/6)), including all labels and controllers. It does not acquire any terminal query, recognize the good label, or promise only one collision globally in the composite ring.

## 1. Exact analytic imports and finite-exception scope

Set r=ceil(N^(1/6)) and B=bit_length(2N)^33. The pinned QRH source is

[The Quasi-Riemann Hypothesis,30 September2026, Corollary1.2](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf).

Its actual statement supplies absolute C,A with least quadratic nonresidue n(p)<=C(log p)^A for every odd prime, and its proof allows A=32. This report treats that pinned analytic claim as an IMPORT/CONDITION, rather than a newly established unconditional result. Consequently, uniformly for odd primes p<=N and all sufficiently large N,

    there is1<=u<=B with (u/p)=-1.                (QRH32)

The extra logarithmic power absorbs C; no numerical value or effective threshold for C is silently supplied. The same consequence and exponent33 palette were used in the journal near37812; they are prior analytic credit.

For an initial small Jacobi-minus discriminant use the already pinned Burgess consequence for the nonprincipal Jacobi character modulo squarefree N. Lau--Wu Theorem1, [primary author preprint](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf), bounds the least unit nonresidue by O(N^[1/(4sqrt(e))+epsilon]). Choose strict exponent slack below5/32. A scan through ceil(N^(5/32)), with gcd tests first, therefore finds a unit of Jacobi symbol-1 for all sufficiently large N. This initial scan is not QRH-dependent.

Statements below about guaranteed orientation are asymptotic under(QRH32). Public size/setup guards and a whole-algorithm finite fallback are specified in Section7. The list itself is not claimed to certify or recognize the analytic finite exceptions without a query or factorization.

## 2. Actually acquire a SMALL negative starting discriminant

First account for the CHANGED moduli, rather than transferring an old small-factor promise. Set M=16*(5r)^2=400r². If M>=N, use deterministic trial division; this is a finite-input branch. Otherwise run a monic integer-block small-factor screen on ALL positive integers1,...,M. With s=ceil(sqrt M), acquire product_(i=1)^s(X+i), evaluate at the actual consecutive block starts0,s,2s,... by monic multipoint evaluation, and clip the final block exactly. This costs soft(s)=soft r. A proper gcd factors; a saturated block is descended or scanned in at most s work. Every individual term is positive and <=M<N, so its gcd cannot be N; thus any nonunit product eventually yields a proper factor. If every block is a unit, BOTH primes exceed M, simultaneously certifying P,Q>16H_D for EVERY later k_D<5r. This paid screen occurs before invoking any controller whose hypotheses need those bounds. No old smaller-k threshold is reused.

If N=3 mod4, use D0=-4. Then (D0/N)=-1. If N=1 mod4, perform the preceding gcd/Jacobi scan for a positive unit a0<=ceil(N^(5/32)) with (a0/N)=-1. Factor this PUBLIC small integer by trial division and select one prime ell|a0 with (ell/N)=-1, which exists by multiplicativity. Its factorization costs at most soft N^(5/64), below r. Set

    D0=-ell if ell=3 mod4,
    D0=-4ell if ell=1 mod4,
    D0=-8 if ell=2.

These are negative fundamental discriminants and (D0/N)=-1 because (-1/N)=+1 in this branch. Their conductors c0=|D0| satisfy c0<=4 ceil(N^(5/32)). Any encountered proper gcd factors immediately. This avoids using an arbitrary already supplied Jacobi-minus integer whose conductor might be too large. Only ONE odd prime ell occurs in D0.

## 3. Positive both-nonresidues flip the orientation without changing negativity

For the proof write the two Legendre signs of an integer t as((t/P),(t/Q)). Start with unknown opposite signs for D0. Under(QRH32), choose u_P<=B with first sign-1 and u_Q<=B with second sign-1. After gcd checks these integers are units modulo N. If either has pattern(-1,-1), that integer itself is a both-nonresidue. Otherwise their patterns must be(-1,+1) and(+1,-1), so their positive product has pattern(-1,-1).

Therefore the EXPLICIT palette

    T={uv:1<=u,v<=B}, including u=1 or v=1,        (1)

contains a positive both-nonresidue t*. It has at most B² polylogarithmically many descriptions. No recognition of either local Legendre symbol is needed. Screen gcd(t,N); a proper gcd factors. Retain only unit t with Jacobi(t,N)=+1, and also retain D0 explicitly. The good t* survives, since(-1)*(-1)=+1. Products with Jacobi-1 are NOT acceptable flips: they would destroy the opposite-sign quadratic-algebra contract.

For each retained t, form negative raw integer D0 t. Let s be its signed squarefree kernel and let D=s if s=1 mod4, otherwise D=4s. Then D is NEGATIVE and fundamental. At the odd primes P,Q the square and possible4 factors removed/inserted have Legendre symbol+1, so

    (D/P)=(D0/P)(t/P), (D/Q)=(D0/Q)(t/Q).          (2)

All relevant factors are units after the gcd checks. Thus (D/N)=-1 for every retained normalized D; t=1 gives the original orientation, while t* flips BOTH signs. At least one retained D has

    (D/P)=-1, (D/Q)=+1,

where P is the SMALLER factor. This proof does not require a sign correction using -t, does not replace the negative discriminant by a positive one, and does not misapply a native colour to a nonunit tag.

## 4. Conductors, factorizations and the changed public modulus

The conductor obeys

    c=|D|<=4 c0 B²=O(N^(5/32) B²).                (3)

The factorization of D0 is known, and all u<=B can be factored together by an ordinary public sieve. Combine their parity vectors to normalize D0uv; every normalization costs polylog N. There is no factorization of an arbitrary N-sized integer at this stage. Gcds and Jacobi/Kronecker tests cost polylogarithmic bits per description. Duplicates may be discarded or retained.

Since1/6-5/32=1/96, (3) is o(r), uniformly over the whole palette. Publicly check c<=r/16 and T_c=max(3,ceil(r/(2c)))>B. These checks eventually hold for every label. Choose an odd prime qpub in one of the two Bertrand intervals at scales T_c and2T_c, excluding prime factors of c, and put

    k_D=2c qpub, H_D=k_D².                        (4)

For sufficiently large N, every odd factor of c except possibly ell divides some uv and is <=B<T_c. Only ell can collide with the two candidate primes, so at least one works. The actual sieve through4T_c and gcd(qpub,c) test are paid. Equation(4) gives r<=k_D<5r under the guard, and c|k_D/2. Thus every label remains fixed sixth-root scale. If any public guard or prime choice fails, take the public finite fallback described below; no invalid modulus is used.

IMPORTANT: c can now have more than one odd prime factor. The old literal sixteen-element square fibers and constant divisor-type count must NOT be reused. Instead v2(k_D) is still in{1,3,4}, odd conductor factors are squarefree, and qpub is coprime to c. The root count for x²=z modulo k_D is at most4*2^[omega_odd(k_D)]<=16B²: all extra odd factors divide uv<=B², with at most the two additional factors ell and qpub. Divisor/content-type counts are likewise polylogarithmic. Exact-delta fibers therefore have POLYLOG width. Grouping/comparing all targets within such fibers costs soft k_D, as does any bounded-width preparation after this inflation. The exact-one minus argument below does not need even this fiber bound.

It is only claimed that the native coordinate/product preparation needed here remains soft k_D. An unrelated old auxiliary theorem requiring a genuinely constant-width ideal is not silently inherited with the same constant16.

## 5. Rebuild and certify every actual family

On the branch where the common small-factor screen has certified P,Q>400r²>16H_D, for EACH label D,k_D execute the already paid scalar rough-controller and norm-one torus supplier, or return any factor they produce. These are the actual factor-or-base routines of `rough-torus-working.md`, SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`, and scalar `rough-index-cancellation.md`, SHA256 `283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0`, with their existing hypotheses. They apply to the actual fundamental D with(D/N)=-1 and c|k_D/2; their order proofs do not require that c have only one odd prime.

They supply actual odd k_D-rough beta and norm-one W with both local orders>16H_D. Rebuild all targets with their new character chi_D, native a,b,parity-repaired a',ell, actual index labels, and q=(beta W)^H_D. Rerun the actual COUPLED seed screen; scalar and torus order bounds alone do not guarantee the coupled split-coordinate orders. A factor ends computation; the continuing branch has all needed1-q^d units through16H_D. No controller, point or seed from D0 is presumed to have transferred automatically to the new algebra.

Keep exactly one native row per unit tag1<=j<k_D, with its original type/index flags, and then its minus subset chi_D(j)=-1. There are phi(k_D)/2 such tags; phi(k_D) need not be a fixed positive fraction of k_D after the small-prime inflation, but is at most k_D and differs by only ordinary soft factors for our acquisition bound. The required signed exponents have O(log N) bits, and native row acquisition is soft k_D. Target norm-fiber handling uses the polylog-width bound in Section4, not a free quadratic pair scan.

The O(B²) labels multiply this work by only a fixed polynomial in log N. Thus the total CONDITIONAL palette/controller/row INPUT acquisition is soft r. It acquires neither the geometric product values nor a rank-k² tensor vector.

## 6. What the good minus-only query actually promises

For a good unknown label D, the smaller prime P is the nonsplit field side. The proved native argument from `implicit-evaluation.md`, SHA256 `5600980cbd17a37e09c79ed9503766cd081df9753bf8593443cc66bc0d4c0646`, now gives EXACTLY ONE minus-colour collision at P. For completeness its decisive arithmetic is short: separating coprime odd scalar/torus orders makes a minus hit satisfy H_D i=a'P+Q+ell as an INTEGER. Multiplying by P and using the native expansion gives

    a'(P-j)²+k_D b'(P-j)=0 mod k_D².

Since a' is a unit, prime-by-prime valuations force k_D|(P-j). Hence j is the own tag P modulo k_D, and the actual q order exceeds the horizon so its index is unique. This proof works for ANY such even k_D; it does not require the older constant-fiber modulus. The own-row coverage proof supplies that hit with0<=i<3H_D+2. Because chi_D(P)=-1 the own tag really is in the retained MINUS subset.

The other prime Q is split. It can have several norm-zero leaves, potentially in different components. Thus the promise is EXACTLY ONE local factor at the smaller nonsplit side, not one global pair or one hit on each side. A saturated product is still localized to an original row/index before the original norm/beta consumer. That consumer's factor-sum bounds use this actual k_D,H_D and repaired horizon; all imported fixed-scale hypotheses remain valid by(4).

The good orientation is NOT recognized by public preprocessing. A future promised unique-intersection routine must have a bounded, verified interface on every supplied label (e.g. return a verified factor/witness or a bounded failure); it cannot rely on an oracle telling which D is good. Run it on the entire list. The ordinary blocked query supplies such an interface today at soft k_D^(3/2), so the palette by itself leaves that exponent unchanged.

Nor does unique local multiplicity imply that a short jet at epsilon=0 determines a deformation's endpoint at epsilon=1. No sparse-recovery or terminal-norm oracle is supplied by this promise.

## 7. Public fallback and exact contribution

The initial Jacobi scan has an explicit cutoff; failure invokes deterministic trial division. Every gcd, conductor/scale guard, modular inverse, controller and coupled seed screen has a defined verified branch. Under the stated imports the scan/size guards fail only for a finite set of inputs. The orientation guarantee from(QRH32) likewise has an unspecified finite-exception range that is NOT publicly recognized from Jacobi symbols alone. For a TOTAL future factoring composition, run all bounded label routines and accept only verified factors/consumable witnesses; if none succeeds, invoke trial division (or the already complete full native query). Under(QRH32) and the promised routine's correctness this fallback occurs only for finitely many N, and its finite cost is absorbed asymptotically. No numerical Burgess/QRH threshold is claimed.

As a standalone preparation theorem, the honest statement is therefore: soft-r input acquisition, with at least one exactly oriented unique-local-hit label for all sufficiently large N CONDITIONAL on the pinned analytic import; finite-input totality belongs to the explicitly defined whole algorithm. This is an actual way to supply the needed promise asymptotically, not a recognition procedure or a new query algorithm.

The known whole-query bound remains soft k^(3/2) on these prepared rows. If an exact bounded-time unique-local-hit solver with soft-k acquisition and original witness support is proved, this polylogarithmic orientation palette would preserve its exponent. Such a solver has not been proved here. This report does not assert an unconditional unverified least-nonresidue bound or a one-sixth factoring theorem.

## Primary cache and preservation

Pinned QRH PDF reused from the already audited exponent-collision packet: `sources/qrh-sept30.pdf`, SHA256 `8fe93046f8cf5ef1ba5969c89addc02d76311adc4ee907509ff9cd96f7ec99e7`. Cached text Corollary1.2 and its A=32 proof were read. Lau--Wu author PDF `sources/lau-wu-2007.pdf`, SHA256 `4cc9dba73064795de434d6b42baca0743347313b6a242f5439c9ed979ddd4368`; its Theorem1 was checked against the primary. No source/shared documents or deployed systems were edited, and no numerical examples were used.
