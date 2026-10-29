# Native torus-annihilator transfer and a complete coprime-order projection

26 October 2026. Scratch paper derivation and primary-source audit. No repository changes, code, numerical tests or Lean.

**Positive result:** every actual nonzero O(log N)-bit annihilator of the supplied large-order norm-one W yields a factor in soft K, using the already supplied scalar beta. This completely repairs the formerly excluded W→W^(N+1) projection. On continuation BOTH torus orders are large, odd, K-rough and coprime across primes; all changed-base screens and native root reacquisition are paid. No numerical order divisor or fast whole collision query is acquired on that successful preparation branch.

The proof uses the original scalar short-order detector and licensed all-semiprime scalar annihilator extractor. Those algorithms and the original point/order preparation are prior credit. The new operation is their explicit native transfer/composition; it is not a generic black-box order theorem. Optional partial-factor calculations are secondary and are not unresolved branches of the completed native algorithm.

## 1. Actual target and unchanged prepared branch

Actual source contracts read: [scalar setup §§1–3](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md), [torus supplier](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-quadratic-ideal-20261024/torus-order-supplier.md), [rough torus extension](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-large-order-recurrence-20261024/rough-torus-working.md), and the frozen pure-modulus preparation. The torus supplier explicitly did not include an N+1 projection; §3 below adds its actual missing factor-return branch rather than claiming that source had proved it.

Keep N=PQ<=K^6, P,Q>16K², K=2*3^e, H=K², and the actually prepared scalar beta and norm-one W in B=(Z/N)[tau]/(tau²-D). Both local orders are odd, K-rough and >16H; beta's cross-prime orders are coprime. At the unknown nonsplit prime R, their orders divide R−1 and R+1 and are coprime. Their coupled order exceeds 256H². All actual short screens remain paid; nothing below substitutes a number for these order promises.

As established in `axis-two-orders.md`, ANY supplied d>1 dividing either good local order suffices: roughness makes d>K, the four smaller-factor residue classes ±1,±N modulo d contain a true factor, and four ordinary AP products through sqrt(N) cost soft K. Such products cannot be saturated because all positive candidates are below Q. This is a useful one-prime conditional input, not a new consumer claim.

## 2. Main theorem: transfer any actual short torus annihilator to beta

Let M!=0 be an ACTUALLY supplied O(log N)-bit integer with W^M=1 globally. Negative M may be replaced by |M|. Let S be the split prime, without any size ordering. Put t=ord_S(W). The original returned W has t>16H, and

    t divides S−1, t divides M.

Let m=S−1 and r=ord_S(beta), so r|m. Elementary prime valuations give

    ord_S(beta^M)=r/gcd(r,M)
       divides m/gcd(m,M)
       <=m/t < S/(16H).

The other factor is >16H, so S<N/(16H). Therefore

    ord_S(beta^M)<N/(256H²)<=K²/256<16H.          (2)

No numerical t, S or local order was computed. This is only a proof of a short-screen coverage promise, using the LARGE split-side order already supplied for W. It does not hold for an arbitrary norm-one point lacking that order bound.

Actually compute gamma=beta^M and run the original scalar short-order detector through C0=16H. Cost is soft K, including the O(log N)-bit powering. Gamma's two local orders remain coprime because the original beta orders are coprime and powering only takes divisors. Equation (2) rules out NoHit. If the detector returns a proper gcd, factor and stop. Otherwise its earliest saturated collision returns an exact COMMON local order c<=C0. Coprimality forces c=1; hence gamma=1 modulo N.

Thus the original, unchanged beta has the ACTUAL global annihilator M. Its two local orders are odd and >16H; M is nonzero and has the required short binary length. Invoke the already licensed all-semiprime scalar annihilator extractor T_ext, costing soft N^(31/192)<=soft K. This is a once-only terminating call, not a polylog operation or a new annihilator theorem. It is applied to beta, not W or an additive trace. All preceding inverses are powers of supplied units; no hidden local inverse, factorization of M or small-index assumption occurs.

The result also handles a supplied annihilator at ONLY the good prime: first compute Norm(W^M−1). A proper gcd factors. A saturated norm is whole identity at BOTH primes because W is norm one, including on its split side; this supplies the global premise above. A unit norm contradicts the promised local annihilation and may return bounded failure in an unpromised attempt.

Consequently every actual nonzero O(log N)-bit torus annihilator is a soft-K factor certificate on this prepared branch. More generally the powering cost is soft(bitlength(M)), but the licensed scalar extractor is only claimed at its stated short-label contract; a wide symbolic descriptor is not silently admitted.

### Consequence for actual short mixed relations

Suppose an actually acquired relation beta^u*W^v=1 holds at the nonsplit prime, with O(log N)-bit integers (u,v)!=(0,0). If u!=0, taking the local quadratic norm gives beta^(2u)=1 there. An actual scalar gcd either factors or supplies the global nonzero scalar annihilator 2u, so the licensed scalar extractor applies. If u=0, then v!=0 and the torus-annihilator transfer above applies after its norm-one gcd test. Thus the same soft-K terminating recovery works without requiring u alone to be nonzero. Equivalently a nontrivial supplied pi^A*barpi^B=1 uses u=A+B, v=A−B; it does not evaluate an unacquired formal relation.

For an actual native row leaf, u=ell+a+bN−Hi and v=ell−a−bN−Hi. If u=0 then v=−2(a+bN), nonzero for the bounded nonzero coefficient rows |a|,|b|<=K<N. Consequently the former zero-scalar-label exception is covered once an actual leaf relation has been acquired. This does not pay for discovering a hit, and does not turn a zero of an unrelated additive observable into a licensed relation.

## 3. Complete the N+1 projection and rebuild the native family

Let R be nonsplit and S=N/R split. Put A0=R+1, B0=S−1 and g0=gcd(A0,B0). The elementary identities

    gcd(A0,N+1)=gcd(B0,N+1)=g0

show that the two local orders of V=W^(N+1) divide A0/g0 and B0/g0, which are coprime. V remains norm one, odd and K-rough. Actually compute V and run the original norm-one short-order screen through 16H, using the usual H-power version if desired (roughness preserves its orders). A proper gcd factors; NoHit supplies both orders>16H. Otherwise earliest saturated collision gives an exact common local order, hence order one. In that case W^(N+1)=1 globally and the main theorem with M=N+1 FACTORS in soft K. Thus continuation supplies both V orders odd, K-rough, >16H and COPRIME without any unresolved branch. The original beta remains unchanged. This is a COMPLETE factor-or-preparation algorithm, not a projection conditional on an unresolved zero case.

Rebuild pi_new=beta*V, barpi_new=beta/V and q_new=pi_new^H. At the nonsplit prime their odd scalar and torus orders divide R−1 and R+1, so are coprime and their product still exceeds 256H². Actually rerun the coupled short-unit screen through 16H, then reacquire the weighted/monic native roots at the new base. All of this costs soft K. The integer stationary phases, lattice coverage and factor-tag proofs are unchanged; the old numeric root values or coupled screen are not reused after changing W.

This gains a genuinely stronger prepared interface—cross-prime coprimality for the torus as well as for beta—and a legal torus-annihilator consumer. It does NOT reveal a numerical local order divisor on the successful branch or evaluate a long collision query at soft K.

## 4. Secondary partial-factor alternative

The native theorem above does not need to factor its exponent at all. The following independent gate is retained for other inputs where only a partly factored multiple is supplied and the native scalar transfer is unavailable.

Suppose the extra acquired input is M=A*C, with M>0, fully factored A=product l^a, gcd(A,C)=1, total supplied bit length L=soft K, and z^M=1 at the good prime, for z=beta or W. C may be completely unfactored. Acquiring these data is additional work, not a native premise.

First compute z^M and its gcd test. For W the norm-one identity makes norm zero exactly WHOLE local identity, including the split side. For beta use ordinary scalar gcd. Since the good prime annihilates, either a proper factor appears or the result is a GLOBAL annihilator. Powers cost O(L) group operations, not polylog merely because M is represented symbolically.

Now compute v=z^C. A proper gcd factors. If v=1 globally, all local orders divide C: the known prime factors in A are irrelevant, and this attempt returns a precisely defined failure. If v has nonidentity at the good prime and not at the other prime, the gcd already factors. Otherwise it is nonidentity at both primes and v^A=1 globally.

Apply complementary-power splitting ONLY to the known prime-power factors of A. At a leaf obtain v_l=v^(A/l^a); then v_l^(l^a)=1. Norm/gcd classification of v_l−1 either factors, is a global identity (skip that prime), or is a unit at both primes. Some leaf cannot be skipped, since A annihilates the nonidentity v and its prime-power factors are coprime. On a unit leaf l divides both original local orders; hence d=l>K is an acquired valid divisor and the four-AP consumer factors. For beta this unit-leaf case is impossible by its supplied cross-prime order coprimality: the splitting therefore necessarily factors earlier. No exact valuation, full order, or factorization of C is needed.

The complementary-power product tree costs soft L ring operations with total exponent-width accounting, as in the already used wide-exponent machinery; all native group/ring operations add polylog N bits. The final AP consumer costs soft K. Thus the composition costs soft(K+L), CONDITIONAL on the supplied partial annihilator and the tested nonidentity z^C. It succeeds exactly when the factored part captures a surviving order prime, or a gcd branch already factors. This is an actual conditional supplier, rather than assuming a divisor as output. On the present native short-annihilator branch it is unnecessary: §2 already factors directly.

Primary algorithmic attribution: [Sutherland, Order Computations in Generic Groups](https://math.mit.edu/~drew/sutherland-phd.pdf), Chapter 7, especially complementary exponent Algorithm 7.3, is the established source for this product-splitting operation. The composite-ring branch proof above is elementary; no field equality oracle replaces its norm/gcd tests. This operation and its wide-exponent complexity are prior machinery, not newly invented order finding.

A useful size regime is a numerical residual C<=K^4: it can itself be fully factored within soft K by the standard deterministic fourth-root integer-factor method, after which the previous fully factored-annihilator algorithm applies. This is conditional acquisition from a small residual integer, not factoring R±1 for free. For a generic O(log N)-bit residual as large as N, that bound is K^(3/2), outside the target. A short binary representation is not a small factorization cost.

The returned native rough bases have not been supplied any such M: the old smooth-killing exponent E removes small primes and is NOT an annihilator of their surviving rough orders. Multiplying it into a descriptor does not change this fact. The old supplier's factored annihilators arise on its factor-return/common-order branches, not on the successful large-order branch. We therefore do not count this conditional composition as a uniform supplier.

## 5. Optional diagnostic: partial factoring of N+1

For comparison only, suppose W^(N+1)=1 and put M=N+1. The direct native transfer already terminates here; the following is an alternative diagnostic, not an unresolved branch of the completed algorithm. There is a concrete additional soft-K gate, stronger than leaving M as an abstract annihilator. Acquire ALL prime-power factors of M with primes at most K², as follows. Use a monic factorial baby/giant product for the integers 2,...,K² modulo the current residual integer. Its cost is soft K. If its gcd is nonunit, localize an actual integer u<=K² with nonunit gcd (a saturated large block is legal); factor gcd(u,M)<=K² by trial division through K, retain the prime factors and remove their entire powers from the residual by exact integer division. Repeat on that residual. Each repetition removes at least one prime factor, so at most O(log N) repetitions occur. All product/MPE divisors are monic; neither candidate separation nor collision values are inverted. The original integer M may have arbitrary composite shape. This acquires a fully factored A and an integer C with

    M=A*C, gcd(A,C)=1, every prime divisor of C>K²,

in soft K total bit cost, with logarithms suppressed. No factorization of R+1 or S−1 was supplied.

Run the §4 test W^C and its known-factor tree. If a prime in the acquired interval K<l<=K² is essential to either local W order, it produces a proper factor or a known l>K and the four-AP consumer. Primes <=K are necessarily irrelevant to these returned rough orders, but extracting the additional interval (K,K²] is a genuinely paid, potentially successful step. All powers and tree widths fit the same soft-K budget.

If this test instead returns W^C=1 globally, both local orders divide C. Since

    C<=M=N+1<=K^6+1,

C has at most TWO prime factors with multiplicity: three primes>K² would give a product at least (K²+1)^3>K^6+1. Test C for primality and an exact square. If C is prime, or the square of a prime, its complete factorization is acquired in polynomial(log N) time and the existing factored-annihilator routine finishes. C=1 contradicts the continuing large-order promise. A perfect-square root here cannot itself be composite, since that would give at least four prime factors>K². The primality branch may use deterministic polynomial-time integer primality; no factoring oracle is invoked.

For this optional partial-factor method alone, the residual case is therefore

    C=l1*l2, l1!=l2, l1,l2>K², hence C>K^4,

with its two numerical prime factors unacquired. There is stronger exact information about the returned W: both local orders divide

    g0=gcd(R+1,S−1)<=min(R+1,S−1)<=P+1<=K³+1.

Any nontrivial divisor of C within that bound is a SINGLE prime, since l1*l2>K^4>K³+1. Both local orders exceed 16K², so they are each a prime. They cannot be different primes: then both l1 and l2 divide g0, forcing g0>=C>K^4, a contradiction. Consequently the hard branch has

    ord_R(W)=ord_S(W)=l,

where l is ONE unknown prime factor of the known distinct-semiprime C, and the other C factor is extraneous to W's order. In particular the actual l must exceed 16K²; the stronger initial screen is retained, not weakened to l>K². This is a common-prime-order conclusion proved from the supplied annihilator and group sizes, not an acquired numerical order.

The same conclusion also follows from individual local group sizes <=N/(16H)+1<K^4, which rule out an order containing two primes>K²; the common-divisor bound above is sharper and establishes that the primes agree. All endpoint inequalities hold on the native K>16 hard branch; no asymptotic exception is required for this classification.

Thus a complete soft-K partial-factoring gate is now executed. It terminates with a factor or reduces the zero branch to a known semiprime C>K^4 and a returned element of unknown common prime order equal to one of its factors. Fully factoring such a generic C by the basic fourth-root engine may exceed K, and no new initialized operation here selects its essential prime. This is a narrower residual problem for that optional factorization method. It is NOT a remaining obstacle to the native algorithm, which uses §2 and terminates without selecting the prime.

## 6. Scope of cyclotomic and generation literature

For an element z of order r, the prime test Phi_l(z)=0 in characteristic not l detects r=l (or the appropriate whole-order cyclotomic condition), not merely l|r. In the norm-one model, with t=W+W^-1 and Chebyshev trace C_l(t)=W^l+W^-l,

    C_l(t)−2=(W^l−1)^2/W^l.

Its vanishing detects the WHOLE local identity W^l=1. The original actual short screen has already excluded that identity through 16H. A prime l dividing a longer rough order need not make either expression vanish. A trace polynomial does not automatically strip the other primary factors.

Given an annihilator M and a prime power l^a||M, the correct primary projection is z^(M/l^a). This explicitly uses the cofactor. The secondary algorithm in §4 weakens the factoring requirement on M but does not omit that input.


The optional small-generator proposal is not used. Wesolowski's ERH [ray-class generator theorem](https://msp.org/obs/2019/2-1/obs-v2-n1-p28-p.pdf), Theorem 1.2, concerns supplied ray-class subgroups and prime ideals; it is not an unconditional small Cayley-parameter generator algorithm. No such conversion, ERH assumption, or full-torus generation premise enters §§2–3. The existing 2M+1 Cayley palette escapes a known kernel M<K and is not being promoted to a whole-group generator certificate.

## Final scope

The main theorem and N+1 projection are complete soft-K factor-or-preparation operations on the actual supplied branch. Scalar beta is unchanged, D is unchanged, and every changed coupled seed is screened again before roots are rebuilt. No factorization of N+1, local R±1, hidden order, full torus generation or additional analytic hypothesis is needed. The optional partial-factor and trace discussions do not qualify this theorem.

What remains unacquired is a numerical local-order divisor or another whole-query readout on the new success branch. Stronger order coprimality is concrete prepared data, not a claim that the long primitive/axis query is now evaluated in soft K.
