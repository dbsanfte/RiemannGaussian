# Explicit lifted roots and a fully charged relation consumer

Scope: the simultaneous lifted-root identity is proved. A conditional congruence-of-squares consumer with a soft-m work ledger is given. No universal smoothness, dependency quality, or improved factoring bound is asserted. This does not reclassify modular roots as integer square discriminants.

## Exact root and size

Let d=m^2, v_j=ell_j-d*kappa_j, with native data and kappa in [0,m). The identity ell_j^2-4a_j N=d Delta_j gives

    v_j^2-4a_j N
      =m^2*(Delta_j-2ell_j*kappa_j+m^2*kappa_j^2).

Modulo m the bracket is Delta_j+4a_j j*kappa_j=0. Therefore

    z_j=(v_j^2-4a_jN)/m^3
       =(Delta_j-2ell_j*kappa_j+m^2*kappa_j^2)/m

is an explicitly acquired integer. In particular v_j^2=4a_jN mod m^3, and

    v_j^2=m^3*z_j mod N.                         (1)

All O(m) v,z descriptors have O(log N) bits and are acquired in soft O(m) bit work in the native scale. A safe elementary bound is |ell|<3m^2, |v|<m^3+3m^2 and

    |z_j| <= [(m^3+3m^2)^2+4(m-1)N]/m^3.

For N=O(m^6), this is O(m^4); the leading N term for fixed a is O(a*m^3). These roots are not close to sqrt(4aN) just because their residues agree modulo m^3.

Antipodal rows have v_j'=-v_j-m^3u with u in {0,1,2}. Hence

    z_j'=z_j+2u*v_j+m^3*u^2.

One may center their common modular root to |v|<=m^3/2 and retain one representative per a. This preserves (1) and costs soft O(m), but the new z values remain O(m^4). It does not supply independent extra norm relations: the exact relation between antipodal entries is displayed above.

## A real congruence-of-squares consumer

First screen gcd(v_j,N). A proper gcd factors N. In the inherited large branch |v_j|<N and v_j!=0, a saturated gcd cannot occur; outside it, retain the explicit finite handling. Equation (1) is the usable scalar relation; a_j disappears modulo N. Factoring a_j alone therefore does not factor the remaining right side of (1).

Choose B=floor(cuberoot(m)), and the factor base consisting of -1, m, and primes p<=B. Strip m powers from every nonzero z_j. Acquire and remove every prime <=B from the remaining parts. If at least pi(B)+3 entries have no residual cofactor, select only that many entries. For each selected relation form the parity column of

    sign(z_j), 3+valuation_m(z_j), valuation_p(z_j) (p<=B).

There are pi(B)+2 coordinates, so a nonempty GF(2) kernel vector exists. Ordinary Gaussian elimination on at most pi(B)+3 rows/columns costs O((B+3)^3)=O(m) bit operations. This deliberately uses a cube-root factor base; generic elimination on an m-sized factor base would not fit the paid bound.

For any resulting subset S, the exact signed integer

    m^(3|S|) * product_(j in S) z_j

is a nonnegative integer square W^2, with W acquired directly from the known prime exponents. Set V=product_(j in S) v_j mod N. Equation (1) proves V^2=W^2 mod N. Compute gcd(V-W,N) and gcd(V+W,N); any proper value factors N. Modular products and powering use only O(m polylog N) work. One may acquire a kernel basis and try its individual basis vectors within soft O(m), because there are O(B) vectors each supported on O(B) rows; this does not justify testing all exponentially many combinations. If all attempted congruences saturate or are units, the consumer reports no factor; it does not assume a nonsaturated dependency.

## Small-prime acquisition is also paid

Directly trial-dividing m norm values by B primes would exceed the desired ledger. Instead sieve the public primes <=B and build their squarefree product M and balanced product tree. Batched integer remainders acquire gcd(|z_j|,M) for every row in soft O(m log N+B log B) bit work. Recursively split each resulting squarefree divisor through the prime-product tree. At a fixed depth, the total bit length of all assigned query divisors is at most sum_j log|z_j|, since each original divisor splits into coprime children; the total bit length of the public tree products is at most log M. Batched remainder/gcd work at that depth is therefore soft O(m log N+B log B). There are O(log B) depths. At prime leaves, divide the original norm value repeatedly to acquire the valuations. Across all values the number of prime-power incidences is O(m log N). Thus this whole small-prime factorization stage has soft O(m) native bit cost, not an unpaid supplied smoothness certificate. No hidden prime factor of N is an input.

## Exactly what remains missing

The family guarantees the norm divisibility (1). It does not here guarantee pi(B)+3 fully smooth residual norms, even after centering. It also does not guarantee that an acquired kernel vector has opposite square-root signs at P and Q. A congruence with V=W in both fields gives gcd(V-W,N)=N; one with V=-W in both fields gives the other saturation. The usual random-relation independence assumption is not licensed for this prescribed public family. No such assumption is made above.

The root modulo m^3 is a root modulo a fully known auxiliary modulus, not modulo an unknown factor of N. Consequently its precision m^3~sqrt(N) does not by itself invoke a hidden-divisor small-root theorem. The previously read divisor-in-residue-class consumers require an acquired residue of a hidden divisor; v_j is instead a root of 4a_jN modulo m^3. Similarly the native sparse-Gauss catalog already supplies modular quadratic rows; it does not certify smooth norms or the sign discrepancy needed by this new relation consumer.

Result: the lifted family yields an explicit, fully paid relation-acquisition and bounded-linear-algebra pipeline with exact sufficient conditions. A theorem forcing its smoothness and nonsaturated square-congruence conditions for every input is still missing. Therefore this is a usable conditional consumer, not an all-input soft-m acquisition algorithm or a factoring-rate advance.
