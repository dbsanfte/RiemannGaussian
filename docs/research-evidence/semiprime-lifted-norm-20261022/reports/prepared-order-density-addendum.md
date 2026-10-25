# Positive-density inputs admitting the full odd/coprime-order promise


The preceding broad-box count can be restricted to inputs that ADMIT a prepared gamma with coprime odd local orders exceeding 16m². This is an existence statement for gamma, not a public acquisition algorithm or a statement about earlier preprocessors.

Take separated fixed intervals I1=[alpha1 M,beta1 M], I2=[alpha2 M,beta2 M] with 0<alpha1<beta1<alpha2<beta2 and all products in [cM²,M²]. Restrict both prime coordinates to 3 modulo 4. Let A_i be their prime counts. Fixed-modulus PNT in arithmetic progressions gives

    A_i ~ (beta_i-alpha_i) M/(2 log M).

There are A1*A2=Theta(M²/log²M) ordered pairs, each corresponding to a unique distinct-prime product because the intervals are disjoint.

We prove a positive proportion have gcd((P-1)/2,(Q-1)/2)=1. These two numbers are odd, so only odd common prime divisors r matter. Fix a cutoff T independently of M. For each odd r<=T, CRT and fixed-modulus PNT for modulus 4r show that the fraction of pairs with P=Q=1 modulo r tends to 1/(r-1)². The union bound over these finitely many r is at most

    sum_(odd prime r<=T) 1/(r-1)²+o(1)
      <=sum_(k>=1)1/(2k)²+o(1)=pi²/24+o(1)<1.

The tail is uniformly small. For T<r<=sqrt(M), Brun--Titchmarsh at x=beta_i M gives an upper bound C_i M/(r log M) for the number of primes in I_i equal to 1 modulo r; dropping the 3 modulo 4 condition only enlarges it. Thus these common-r pairs total at most

    C M²/log²M * sum_(integer r>T)1/r²
      =O(M²/(T log²M)).

The constants depend only on the fixed intervals. Choose T large enough that this is less than, say, one quarter of (1-pi²/24) times the main pair count.

For r>sqrt(M), the elementary bound on integer candidates in each interval is C_i(M/r+1). Since r<=beta2 M whenever it divides both P-1 and Q-1, summing over ALL integers r in that range, rather than just primes, bounds these pairs by

    O(sum_(sqrt(M)<r<=beta2 M)(M/r+1)²)
      =O(M^(3/2)+M log M+M)
      =o(M²/log²M).

Combining the finite small-prime union bound with the two tails leaves a fixed positive fraction of all pairs. In particular there are Omega(M²/log²M)=Omega(m^6/log²m) distinct products satisfying both congruences and the coprimality condition. Since the norm-consumer success count is only m^{5+o(1)}, most of this restricted family also defeat the specified norm pair/singleton screen.

For each such P,Q the maximal odd subgroup orders are A=(P-1)/2 and B=(Q-1)/2. They are odd and coprime, and A,B>16m² for sufficiently large m because P,Q are constant multiples of m³. Choose local generators of these odd subgroups and combine by CRT to obtain gamma. Thus these inputs admit the stated prepared local orders. This construction is proof-side existence: no cost-free acquisition of the generators or factors is claimed.

This closes the gap between bare balanced inputs and existence of a base satisfying the full odd/coprime local-order promise. It still does NOT show failure of the whole factoring controller: an earlier authorized preprocessing branch might already factor the input. It also does not address the literal least-prime selector bin, adaptive moduli, higher dependencies, or a consumer using extra properties of the acquired gamma.

Analytic sources used: Montgomery--Vaughan, *The large sieve*, Mathematika 20 (1973), 119--134, Theorem 2 (Brun--Titchmarsh), author-hosted PDF https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf and DOI https://doi.org/10.1112/S0025579300004708 . For fixed-modulus PNT in progressions, the stronger primary theorem of Thorner--Zaman, *Refinements to the prime number theorem for arithmetic progressions*, arXiv:2108.10878v2, https://arxiv.org/abs/2108.10878v2 , supplies the standard fixed-modulus consequence used here. Only fixed 4 and finitely many fixed 4r need asymptotics; no uniform PNT over growing moduli is asserted. The growing-modulus tail uses Brun--Titchmarsh and the elementary integer bound instead.

Convenient single primary source for BOTH analytic inputs (independently checked by root): Lenstra--Pomerance, *Primality testing with Gaussian periods*, 24 August 2017, section 11, page 35, https://math.dartmouth.edu/~carlp/aks240817.pdf . The section states fixed-q PNT in progressions and Lemma 11.1 gives pi(x;q,a)<=2x/(phi(q) log(x/q)). Applying its lemma with x=beta_i M and q=r<=sqrt(M) gives exactly the tail estimate above. The order of quantifiers is fixed T first, M tending to infinity second, then the arbitrarily small fixed tail bound; conjectural uniform asymptotics are not needed.

## Refinement: preserve the native q orders as well

The common-H setup also requires both local orders of q=gamma^(m^2) to exceed 16m². Remove pairs for which P=1 modulo m or Q=1 modulo m. Since m=M^(1/3)<=sqrt(M), the same Brun--Titchmarsh bound gives O(M/(m log M)) such primes in either fixed coordinate interval. Multiplication by the O(M/log M) prime choices in the other interval shows that the removed pairs number

    O(M²/(m log²M))=o(M²/log²M).

The positive-density conclusion is therefore unchanged. As m is odd, the remaining primes satisfy gcd(m,A B)=1 for A=(P-1)/2 and B=(Q-1)/2. Choose gamma's local orders to be exactly A and B as above. Then ord_P(q)=A and ord_Q(q)=B: raising to m² leaves both orders unchanged. They remain coprime, odd, and greater than 16m². Consequently ord_N(gamma)=A B>256m^4 as well.

All these are existence properties of CRT-combined local generators. This refinement does not acquire those generators, replace the paid preparation routine, prove failure of any earlier factor screen, or extend the fixed-modulus result to the literal auxiliary selector.
