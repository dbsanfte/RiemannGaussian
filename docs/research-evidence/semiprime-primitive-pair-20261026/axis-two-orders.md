# Axis readout from two supplied groups: exact controller and missing order data

26 October 2026. Scratch paper analysis; no repository edits, tests, implementation or new point/order oracle. Read the frozen fused-readout README, pure-weighted/common-tag and quadratic-lift interfaces, and the axis-supplier parameterized-controller. **No new all-input soft-K axis algorithm is obtained.** The concrete useful extra input identified below is a certified one-prime partial order divisor, not full orders or a common orientation.

## 1. Keep the actual prepared groups

Use pure K=2*3^e, H=K² and the actually paid preparation: pi=beta W, barpi=beta/W, N=PQ<=K^6, P,Q>16H, beta scalar, W norm one, both odd K-rough local orders>16H. At the unknown nonsplit prime R the two orders r_beta,r_W divide R−1,R+1 and are odd, hence coprime. Thus ord_R(pi)=r_beta*r_W>256H². The original scalar beta orders at the two primes are also coprime. These are lower bounds and algebraic promises, not acquired numerical orders.

For the horizontal shortest axis (a,b)=(K,0), the actual phase is ell=-Kj modulo H. Write the actual centered phase ell=-Kj+H*k_j. K-power injectivity gives the exact good-field query

    barpi=pi^x, x=j+K*(i-k_j).

Equivalently use centered colour c_j=j-K*k_j, so x=c_j+Ki. The known carry belongs to the index transport; the original physical i does not generally give x=j+Ki.

Negative axes reverse the signed index and are equivalent after retaining endpoints. Norm and norm-one parts separately give

    beta^(R−1)=1, W^(R+1)=1.

Conversely a tested exponent x satisfying pi^x=barpi at the good field is congruent to R modulo r_beta*r_W, not merely modulo one of the two orders. This explains the strong no-alias provenance. It is not a supplied residue of R modulo an acquired modulus.

For a vertical axis put c_j=[N*j^-1]_K, a public permutation of unit colours, and write ell=-K*c_j+H*k_j. The exact transported exponent is x=c_j+K*(i-k_j). Use the complementary exponent: barpi^N=pi^(N/R) at the good field. Its norm equations are beta^(x−N)=1 and W^(x+N)=1. Thus either axis orientation is a bounded logarithm for pi with a known target and a factor or complementary-factor exponent. All bases and targets are paid.

## 2. Execute the complete colour AP collapse without an order fiction

Every unit colour modulo K is congruent +1 or −1 modulo 6. For the original physical interval [-M0,M0], use the exact carry transport above. A lawful common overcover is |x|<=K*(M0+1), since centered colour has absolute value at most K/2. This is an overcover, not equality with an unshifted j+Ki union. For a supplied positive factor/complement bin [L,U], retain the integers of that bin instead. For rho in {1,5}, define

    t_min=ceil((L-rho)/6), t_max=floor((U-rho)/6).

If t_min<=t_max, acquire x=rho+6t for t_min<=t<=t_max, length t_max-t_min+1, known start pi^(rho+6t_min) and base pi^6. Empty strings are omitted and all tails are clipped literally. The analogous vertical target is barpi^N with the public reciprocal colour permutation. These at-most-two scalar GP strings are lawful axis overcovers because the true factor/complement exponent is a unit modulo K and belongs to its correct public bin. There is no auxiliary root of unity and no undeclared carry deletion.

A string of length T can be acquired and tested by monic baby/giant product evaluation in soft sqrt(T), without inverting any geometric node difference or collision value. If a norm gcd is proper, return it. Otherwise localize a saturated value using the same product tree. At a saturated leaf the nonsplit component is zero. In a factor/complement range contained in [1,N/(16H)], both its tested exponent and the actual factor are less than K^4/16, while ord_R(pi)>256K^4. Therefore the congruence forces equality as INTEGERS, and gcd(x,N) returns a proper factor. No generic beta annihilator is needed for this promised leaf. Wrong target/bin attempts return only checked factors or bounded failure.

The scalar collapse is exact for the chosen completed exponent union; it is not equality with a masked original subset. It is safe as an axis overcover because every added tested exponent keeps that integer-size decoder. Its length can exceed 16H. Hence one may NOT infer globally unit short differences, a one-hit count at every split component, or a simple global hit-mask flag from the original short q screen. The good nonsplit large-order argument suffices for the zero/nonunit factor controller just described. The monic engine does not require those unavailable global units.

The resulting bill is still soft sqrt(B) on a factor exponent bin of scale B. Combining the already initialized HH alternative retains soft min(sqrt(B),N^(1/5)). This section is an executed finite normalization and guard check, not a new DLP complexity gain.

## 3. A weaker additional input than two full orders would suffice

Suppose one additionally ACQUIRES a positive integer d>1, with O(log N)-bit representation, together with a valid promise that d divides either r_beta or r_W at the nonsplit prime. It need not divide either order at the other prime, and which of the two groups is used may be unknown. K-roughness implies d>K. Consequently

    R=+1 or −1 modulo d.

For the smaller factor P, either this is already P's residue or complementing gives P=+N or −N modulo d. Thus the FOUR acquired residue classes {+1,−1,+N,−N} modulo d contain a true smaller-factor tag. This does not require a common local order, exact order, unique collision, or nonsplit-side identification.

There is a direct initialized soft-K consumer independent of any projected beta order. If d>sqrt(N), each class contains at most one positive candidate below sqrt(N); test them by gcd. Otherwise acquire the at most four APs x=s+d t through sqrt(N). Since d>K and sqrt(N)<=K³, their total length is O(K²+1). A monic AP-product baby/giant factorial test costs soft sqrt(length)=soft K; no AP node separation is needed. A proper product gcd factors. Indeed a saturated product is impossible here: every positive candidate x<=sqrt(N)<Q, so no term, and hence no product, is divisible by Q. Ordinary product gcd suffices; singleton cases may use direct gcd tests. No saturated-localization premise is needed in this consumer. If gcd(d,N)>1, first return that verified factor. Residue zero is also handled directly. All starts, ceilings, divisions and candidate checks are paid.

This conditional theorem is narrower than an order oracle. The old torus supplier already exploits an actually acquired common raw order, so it must not be credited as a new common-order factoring result. The potentially weaker missing data here are a ONE-PRIME divisor, already enough to make a four-element palette. No such divisor is currently supplied on the successful hard branch: its roughness deliberately removes every small prime factor, and returning a nontrivial divisor of a hidden remaining local order is a separate acquisition task.

## 4. Execute the two-order search idea and locate its cost

The two defining equations are testable at a proposed x by binary powering. A baby/giant search can keep both coordinates: test beta^(x−1)=1 and W^(x+1)=1 jointly, or equivalently pi^x=barpi. At the nonsplit field the product of the two coprime orders makes that equivalence exact. Keeping both coordinates does not produce known congruences x=1 mod d_beta and x=−1 mod d_W until such numerical divisors are acquired. Their coprimality does not make either numerical modulus computable.

In particular, a CRT construction from the symbols r_beta,r_W is NOT initialized. Computing r_beta or r_W by a long order screen pays its own bounded-order work; the current generic deterministic collision engine on a scale-B interval costs soft sqrt(B), the same as the executed axis string. The already performed screen stops at 16H and returns only exclusion of smaller orders, not a remaining large factor of an order. Reusing its discarded smooth exponent supplies no nontrivial divisor of the rough returned orders. Cross-prime coprimality of the beta orders ensures useful factor-return branches when an actual common relation is found; it supplies no public nontrivial order divisor on this continuing branch.

Thus the concrete composition is: acquired one-prime divisor -> four factor-residue APs -> soft-K factorer. The first unpaid operation is acquisition of that divisor (or another equally informative bounded palette), not CRT, phase transport, AP endpoints or the factor consumer. No universal partial-order supplier, new rate, or lower bound on all two-group algorithms is asserted.
