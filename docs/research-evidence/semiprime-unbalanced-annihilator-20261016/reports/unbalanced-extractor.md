# A short-annihilator extractor without a balance hypothesis

2026-10-16. A classical conditional factoring algorithm. This extends the previously paid balanced short-annihilator interface by using dyadic caps and the universal separator. It does not acquire the supplied annihilator.

## 1. Precise input and conclusion

Let N=P Q for distinct odd primes. Let m>=1 be a public integer with N<=m^6 and m=Theta(N^(1/6)), with fixed comparison constants. Put B=16m². The inputs also include a unit gamma modulo N whose exact local orders r_P,r_Q are both odd and greater than B, and a nonzero integer K with gamma^K=1 modulo N. Assume the explicit binary length of K is at most a fixed power of log N. No factor, order, order factorization, balance bound, primality of the local orders, coprimality of the local orders, or individual index bound is supplied.

There is a deterministic algorithm factoring every such promised N in soft O(N^(31/192)) bit operations, hence in soft O(m). The hidden constants may depend on the fixed exponent bounding the input length of K and on the fixed sixth-root scale constants. All logarithmic factors, input reads, gcds and modular powers are charged. This is an asymptotic theorem with a finite-input fallback, not an effective numerical Burgess threshold or practical runtime assertion.

Write K_0 for the positive odd part of |K|. Since r_P,r_Q are odd and divide K, both divide K_0. For any unit a, set b=a^(K_0) modulo N. If v_P=(P-1)/r_P, then

 b^(v_P)=a^((P-1)(K_0/r_P))=1 modulo P.

Thus ord_P(b) divides v_P; the analogous assertion holds at Q. Odd powering preserves the full 2-primary part of the local order of a. These conclusions require no coprimality between a local order and its index.

## 2. Universal separator with only one small local order

Use the previously proved monic baby-step/giant-step separator with cap M>=1 and H=ceil(sqrt M). It always returns a proper factor, an EXACT common local order ord_P(b)=ord_Q(b)=c<=H², or NoHit. NoHit certifies that BOTH local orders exceed H². Its bit cost is soft O(sqrt M log N), allowing ordinary logarithmic factors in M,N.

The old report initially states a both-small promise, but explicitly proves correctness of every output outside that promise. In particular the same algorithm guarantees a hit if only min(ord_P(b),ord_Q(b))<=M. Here is the required reasoning: its rows cover all positive exponents 1,...,H². The first nonunit row and larger-baby-index-first descent inspect these exponents in increasing order. A proper gcd factors. A saturated leaf at exponent c, with all smaller exponents certified units, forces c=min(ord_P(b),ord_Q(b)) and forces both orders to divide c; hence both equal c. NoHit is impossible if either order is <=M. Repeated nodes and zero divisors do not invalidate its monic remainder arithmetic. In particular no bound on the OTHER order is necessary.

## 3. Analytic input with strict slack

Lau–Wu, Theorem 1, printed page 2 of the pinned author preprint, states the Burgess least-character-nonresidue bound for every nonprincipal character of cubefree modulus: for every epsilon>0 its least nonresidue is O(q^(c_B+epsilon)), where c_B=1/(4 sqrt(e)). The character value at that integer is neither zero nor one. The proof for composite cubefree moduli is in Section 2, printed pages 4–6. Primary: https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf . Fingerprints are in source-pins.json via the already preserved primary metadata; no full paper is newly copied here.

Fix epsilon>0 with c_B+epsilon<5/32. The Jacobi character modulo N is a nonprincipal primitive quadratic character because P,Q are distinct odd primes. N is squarefree, hence cubefree. Therefore a Jacobi-minus-one unit occurs by N^(5/32) for all sufficiently large N, after absorbing the uniform implied constant using the strict exponent margin.

The same theorem applies to the Legendre character at either hidden prime ell. Uniformly whenever ell<=Y and Y>=sqrt N, its least nonresidue is <=Y^(5/32) for all sufficiently large N: the bound C ell^(c_B+epsilon)<=C Y^(c_B+epsilon)<=Y^(5/32) holds uniformly as Y tends to infinity. This uniformity is important because the dyadic bin varies with N. No GRH, prime-order condition, or prime-distribution assumption is used.

## 4. Explicit algorithm

All cutoffs below are rounded UP and computed by fixed integer powers and roots; floating-point approximations are unnecessary. A scan first computes gcd(a,N). A proper gcd immediately factors; gcd N is skipped; only units are powered or passed to the separator.

1. If K=0, invoke trial division; otherwise strip K to K_0. Scan 1<=a<=ceil(N^(5/32)), computing gcd and Jacobi symbols only, until a unit a_0 with Jacobi(a_0,N)=-1 is found. If none is found, invoke deterministic trial division as the fallback. Compute b_0=a_0^(K_0) once.

2. Enumerate every power of two X with B/2<=X<=sqrt N. For each bin set M_X=ceil(2X/B) and Y_X=ceil(N/X). Run the universal separator on b_0 with cap M_X. A proper factor ends the algorithm. NoHit skips this bin. An exact common-order output starts step 3 for this bin.

3. Scan every 1<=a<=ceil(Y_X^(5/32)). Handle gcds as above. For each unit compute b=a^(K_0) and run the separator with cap M_X. Return any proper factor. Continue after either NoHit or an exact-common-order result. After the scan proceed to the next bin.

4. If all bins fail, use deterministic trial division. All control branches are defined without knowing the hidden factors or a Burgess threshold.

## 5. Correctness of the successful bin

Relabel P<Q for the proof. Since ord_P(gamma)>B, P-1>B. Let X be the largest power of two not exceeding P. Then X<=P<2X, X>P/2>B/2, and X<=P<sqrt N. Thus this correct bin is enumerated, and its cap satisfies

 v_P=(P-1)/r_P<P/B<2X/B<=M_X.

For every unit a, ord_P(a^(K_0))<=v_P<M_X. Consequently the correct bin's separator can never return NoHit, regardless of the possibly unbounded Q-side order. Rounding and strict inequalities create no endpoint gap.

Put s_P=nu_2(P-1), s_Q=nu_2(Q-1). For a prime ell, a quadratic nonresidue has local order with 2-part exactly 2^(nu_2(ell-1)); a quadratic residue has local order whose 2-part is at most half that value. These statements follow by writing a in a cyclic local multiplicative group. Odd powering leaves those 2-parts unchanged.

If s_P=s_Q, the Jacobi-minus-one base has opposite Legendre signs and hence unequal local 2-primary orders. The correct bin must therefore return a proper factor on b_0: NoHit is impossible and an exact-common-order output is impossible.

Otherwise the valuations differ. More generally ANY bin producing an exact-common-order result on b_0 proves that s_P!=s_Q, because equal valuations contradict the opposite Legendre signs. Let ell_* be the prime with the larger valuation. In the correct bin both primes are <=N/X: Q=N/P<=N/X and P<=Q. Hence ell_*<=Y_X, and Y_X>=sqrt N. For all sufficiently large N, the phase-3 scan contains a Legendre nonresidue at ell_*. At that base the local 2-primary order at ell_* is strictly larger than the maximum possible 2-primary order at the other prime. After odd powering the two orders remain unequal. The correct-bin separator must return a proper factor. Gcd discoveries can only terminate earlier with a factor.

Thus for all sufficiently large promised inputs a bounded scan succeeds, in both valuation cases. Wrong bins can safely return NoHit or common orders: their results are sound, and they neither change the input nor suppress the correct bin.

## 6. Full bit clock and finite-input totality

There are O(log N) bins. In every enumerated bin X>=B/2, so M_X=Theta(X/B), including the endpoint where M_X=1. Also X<=sqrt N and Y_X=ceil(N/X)=O(N/X). One separator costs soft O(sqrt(X/B)) bits because residue and index lengths are O(log N). Every trial gcd and exponentiation by K_0 costs polylog N bits under the explicit input-length bound. Therefore phase 3 for one bin costs

 soft O((N/X)^(5/32) sqrt(X/B))
 =soft O(N^(5/32) X^(11/32)/m)
 <=soft O(N^(5/32+11/64-1/6))
 =soft O(N^(31/192)).

The constant factor sqrt B=4m and rounded cutoffs do not alter this estimate. This bound also covers the per-base gcds and modular powers since M_X>=1. The preliminary separator in each bin costs at most soft O(N^(1/4)/m)=soft O(N^(1/12)). The initial cheap Jacobi scan costs soft O(N^(5/32))=soft O(N^(30/192)), plus one polylog-bit modular power. Input reads, stripping K and bin/cutoff construction cost polylog N and are included. Multiplying by O(log N) bins changes only suppressed logarithms. Finally 31/192<32/192=1/6.

Burgess guarantees the required nonresidue bound uniformly over all enumerated bin bounds; the correct bin therefore succeeds for every sufficiently large promised input. Trial division therefore runs only on a finite set of promised N. With the fixed polynomial bound on K's binary length there are finitely many such input strings. Their costs are absorbed by a fixed asymptotic constant; the algorithm need not know the threshold. Outside the promises the algorithm still terminates by trial division, but no claimed fast bound applies there.

## 7. Exact contribution and limits

The balanced predecessor required BOTH local indices<m. The extension uses only one index bound in the correct public dyadic bin, and obtains it from the smaller prime. Neither a balance restriction nor any global index bound is assumed. The reusable separator proof and Burgess input are inherited; the new paid composition is the dyadic unbalanced recovery interface and its uniform worst-bin clock.

This theorem assumes a supplied nonzero polylog-bit GLOBAL annihilator of the specified gamma. It does not acquire K, infer K from a local certificate, establish original-family collision coverage for a changed base, solve the long q-product query, or assert the full Lean/bit-complexity objective. No previously frozen report or repository source is modified.
