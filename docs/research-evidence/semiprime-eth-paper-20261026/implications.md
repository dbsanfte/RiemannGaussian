# Study of the supplied ETH draft: factoring thresholds and an exact macro-FFT bridge

26 October2026. Supplied draft: *The Exponential Time Hypothesis Is False*, OpenAI, dated17 October, revised25 October2026, 67 pages. This report treats its results CONDITIONALLY; it does not independently validate its SAT/tensor-contraction proof. The factoring goal remains PAUSED. No repository edits, factoring runs, or algorithm implementation.

**Main result of this study:** the ordinary multiplication-to-3SAT reduction does not by itself reach the N^(1/6) target. However the draft's stronger AppendixD TheoremD.1 admits an exact O(L)-WIRE multiplication tensor network with polynomial-time macrovertices of degree O(L^(3/4)). If TheoremD.1 is correct with its stated uniform input contract, that network yields deterministic factoring in 2^O(L/sqrt(log L)) time and polynomial space, L=ceil(log2(N+1)). This is a conditional implication of the supplied theorem, not an unconditional factoring result or resumed goal work.

## 1. What the theorem actually says

Theorem1.1, printed p2, gives for each FIXED clause width k a deterministic exact counter with polynomial space. Its general bit-time exponent is O_k(n log log n/sqrt(log n)); when m≤Dn for FIXED D it is O_(k,D)(n/sqrt(log n)). Positive count yields decision, and variable-by-variable self-reduction finds a witness with polynomial overhead. The constants depend on fixed k,D, not on N.

Section6.4 and Lemma6.3 pp43–44, proved in AppendixA pp44–47, sparsify a formula into a DISJOINT partition of its satisfying assignments, on the SAME n declared variables. This controls clause density and count multiplicities. It does not delete arithmetic-verifier auxiliary variables. Section5/Theorem2.2, pp20–21 and35–39, concerns sparse fixed-degree equations over F2, with O(n) equations and polylogarithmically many monomials per equation. Integer multiplication cannot be silently replaced by characteristic-two multiplication: integer carries must still be verified or encoded.

AppendixC.2 pp52–53 applies to Boolean maps whose EACH output depends on a FIXED number d of input bits. It preserves the original n variables because each local truth table becomes constant-width clauses. Ordinary integer product bits do not satisfy that locality promise. Making the multiplier's gates local introduces its internal variables again.

## 2. Rigorous SAT-encoding threshold for the target

Let a uniformly constructed sparse fixed-width factor-verifier CNF have v(L) total variables, m≤D v(L), and polynomial-in-L construction/output overhead. Include ALL gate, carry and witness variables in v. The paper's sparse-SAT route then gives

    log2 T ≤ C v(L)/sqrt(log v(L))+O(log L)

for a fixed but unspecified C. To establish a runtime strictly below 2^(L/6) by this bound without knowing C, it suffices that

    v(L)=o(L sqrt(log L)).                         (1)

At v=c L sqrt(log L), one needs the actual constant Cc<1/6 (with the natural/base2 logarithm conversion included); an O-bound alone does not prove the comparison. For v=O(L(log L)^alpha), alpha<1/2 suffices asymptotically, alpha=1/2 is constant-sensitive, and alpha>1/2 does not give the target from this estimate.

An explicit schoolbook gate/carry encoding has O(L²) variables and clauses and unique extension per factor pair, but its resulting guarantee is 2^O(L²/sqrt(log L)), far too large. Even GRANTING an O(L log L)-size Boolean multiplication circuit and sparse Tseitin encoding, the bound is 2^O(L sqrt(log L)), also insufficient. A faster BIT multiplication algorithm is not automatically a same-size Boolean circuit without checking its simulation model; this caveat only weakens that route. Primary comparison: Harvey–van der Hoeven, *Integer multiplication in time O(n log n)*, Annals2021, explicitly uses a multitape bit model: https://annals.math.princeton.edu/2021/193-2/p04 .

No verified factor-specific fixed-width encoding with o(L sqrt(log L)) TOTAL variables was obtained in this study. In particular the factor witness length O(L) is not the verifier's Tseitin variable count. The positive construction below uses a different input interface genuinely allowed by AppendixD.

## 3. A smaller VERIFIED encoding in the AppendixD wire model

### 3.1 Exact finite ring and parameters

Even N is handled directly by testing divisibility by2, and N≤3 is trivial. Uniformly define L=ceil(log2(N+1)), so N<2^L even at powers of two. For the remaining odd inputs this is also their usual bit length. For L≥2, let n be the smallest power of2 at least4sqrt(L). Then

    4sqrt(L)≤n≤8sqrt(L), b=n/4, d=ceil(L/b)≤n/4.

Encode each candidate factor by d base-2^b digits, padding its top unused bits with zero so it is an L-bit integer. Use the explicitly known auxiliary ring

    R=Z/(2^n+1)Z, word length n+1 bits, omega=4.

Since n is a power of2, omega^(n/2)=2^n=-1 in R, and omega^n=1. These are PRINCIPAL roots, not merely formal order assertions: for each0<a<n, write a=2^v a_odd; pairing half-period terms gives sum_(j<n)omega^(aj)=0. The integer n is a unit in this odd modulus, with its inverse found by the ordinary extended gcd. Thus the DFT and inverse DFT are exact over R despite its possible compositeness. No prime search, unknown-factor field, modular square-root oracle or order finder is used.

Pad each factor's digit vector with zeros to length n. Its cyclic convolution is its ORDINARY convolution because its degree is at most2d-2<n. Every coefficient is nonnegative and

    coefficient < d*2^(2b)≤(n/4)*2^(n/2)<2^n<2^n+1.

Thus no coefficient wraps in R. Its canonical inverse-DFT residue is the true INTEGER convolution coefficient.

### 3.2 Constant-stage macro-FFT architecture

Factor n=r t with r=2^floor(log2(n)/2), t=2^ceil(log2(n)/2), so max(r,t)≤sqrt(2n). Write input index j=j1+r j2 and output index k=k2+t k1. The finite identity is

 y_(k2+t k1)
   =sum_(j1<r)(omega^t)^(j1 k1) omega^(j1 k2)
          *sum_(j2<t)x_(j1+r j2)(omega^r)^(j2 k2).

It realizes the n-DFT by t-point transforms, pointwise twiddles and r-point transforms. Each transform is ONE tensor vertex checking all its input/output words. It has at most2max(r,t)(n+1)=O(L^(3/4)) bit ports. Its 0/1 truth-table ENTRY is computed on demand by a direct finite DFT, in polynomial time and space in L; its exponentially large table is never emitted. The inverse uses omega^-1 and folds n^-1 into its final stage.

Use two forward transforms, n pointwise product-mod-R vertices, and one inverse transform. The pointwise vertices have3(n+1)=O(sqrt L) ports and polynomial-time entry checks. The number of word interfaces in these fixed stages is O(n); their TOTAL bit-wire count is O(n²)=O(L). Macrovertex entry checks are exact, not approximations to complex FFTs.

### 3.3 Digit constraints, integer carry chain, and unique extension

At each input word, a validity vertex enforces the b-bit digit bound (or its shortened top-digit bound); the padded words equal zero. A local flag says that the represented factor is at least2: in digit0 it tests digit≥2, and at higher digits it tests nonzero. A Boolean OR chain forces the OR of these flags to1, for each factor. This excludes0 and1 without a large-arity global tensor.

Let c_k be the canonical inverse-DFT coefficient. Append the INTEGER constraints

    c_k+u_k=N_k+2^b u_(k+1), 0≤k<n,
    u_0=u_n=0,

where N_k is the fixed base-2^b digit of N (zero beyond its length). Each carry word uses n+1 bits and each constraint has3(n+1) ports. True carries are bounded by d*2^b<2^n, so this capacity suffices. The initial carry and the equations determine all carries uniquely. Summing the equations times2^(bk) proves that they hold exactly iff the candidate INTEGER product equals N. These tests are not performed modulo2 or moduloR.

All intermediate residues are required to be canonical integers in[0,2^n]. Therefore every valid ordered factor pair has exactly ONE internal extension: forward transforms, twiddles, products, inverse transform, flags and carries are deterministic. Conversely every satisfying assignment gives a pair p,q≥2 with p q=N. The network count is exactly the number of ordered nontrivial factor pairs, at most2^(2L). For the native distinct semiprime it is2.

The carry chain adds O(n) words; the OR flags add O(n) bits. Subdivide EVERY bit-edge by a degree2 equality tensor. This makes the graph bipartite, doubles its edges and preserves its count bijectively. A conservative count is at most100n²≤6400L bit-edges; the exact constant is immaterial but fixed. Every vertex degree is at most100L^(3/4).

## 4. Apply the paper's precise tensor theorem

**Source:** AppendixD.1 p53, TheoremD.1; its promised algorithm and exact arithmetic are developed in AppendixD and AppendixB. Its parameter is NUMBER OF WIRES, not Tseitin gate count. It permits maximum degree≤ceil(s^(9/10)) and implicitly described tensor entries computable in polynomial times 2^(A s^(9/10)), for fixed constants. Our entries are 0/1 and polynomial-time computable.

Choose

    s=1024L, P0=2L+1, ell=1,

and compute the contraction in Z/2^P0 Z, an allowed special case of the theorem's ring. The edge count fits a fixed constant C times s. Also

    100L^(3/4)≤512L^(9/10)=s^(9/10)

for L≥1, so there is no vague sufficiently-large degree exception. P0≤s. The graph, port lists and entry descriptions have polynomial length; there are polynomially many vertices. All TheoremD.1 input conditions are thus met by the EXPLICIT macro-FFT encoding. The counting modulus does not change the integer checks inside each local 0/1 predicate.

Because the true count is below2^P0, its least nonnegative modular value is exact. CONDITIONAL ON THEOREM D.1, one count costs

    2^O(L/sqrt(log L)) bit operations, polynomial space.

When the count is positive, fix the free INPUT DIGIT bits one at a time, retaining a bit if the conditional count stays positive. This changes only the local input-validity predicates and makes O(L) sequential queries with the same wire and degree bounds. Recover p, compute q=N/p and verify the product. Space stays polynomial. This is deterministic all-input witness recovery, not sampling or a heuristic success campaign.

Consequently, IF the supplied tensor-contraction theorem is correct as stated, the factoring time is 2^o(L) and is below2^(L/6) for all sufficiently large L, regardless of its hidden fixed constant. The result does not need the native stationary family, orders or HH residue consumer. It is a conditional paper consequence, not an implemented algorithm or independent validation of TheoremD.1. Its constants and practicality are unspecified. This implication deserves independent checking of the network and of the source theorem; it must not be weakened to the incorrect claim that a quasilinear Tseitin formula already suffices.

## 5. Broader implications, with scope kept conditional

If Theorem1.1 is true, the implications explicitly explained in §1.1.1–1.1.3 pp4–5 follow: ETH, #ETH, SETH, Gap-ETH and NSETH in the stated fixed-width senses fail. Their former use as assumptions does not prove the corresponding target problems now have faster algorithms. A reduction in the OTHER direction, with the right parameter blow-up, is required. OVC and hypotheses about unrestricted-width CNF are not automatically refuted by a fixed-k result; the draft itself makes this distinction. Unconditional lower bounds for restricted proof systems remain unaffected.

The theorem does NOT prove P=NP, NP=coNP, #P=FP, polynomial-time factoring, or superpolynomial circuit lower bounds for NP. AppendixC.1 pp51–52 derives a language in E^NP with infinitely-often circuit size greater than c n sqrt(log n), using its SAT speedup and hierarchy argument. This is a different class and conclusion. AppendixC.2 inverts constant-output-locality maps in subexponential time, which rules out exponential inversion hardness for that family but not polynomial-time one-wayness.

The macro-FFT consequence above, if valid, likewise does not break the STANDARD polynomial-time hardness definition of RSA/factoring-based cryptography. It improves an asymptotic exponential-time guarantee, with no concrete security-level constants supplied. It would contradict a posited2^Omega(L) worst-case factoring lower bound, but ETH was not itself a theorem establishing that bound. No empirical cryptographic attack or goal progress is claimed here.

**Study priority:** independently audit TheoremD.1's implicit-high-arity tensor input model and this O(L)-wire construction. The ordinary sparse-SAT threshold(1) remains correct; it is the stronger allowed macrovertex interface that supplies the conditional positive bridge.
