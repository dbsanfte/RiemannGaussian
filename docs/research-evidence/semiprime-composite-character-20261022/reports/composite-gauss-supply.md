# Composite character order repairs auxiliary supply for the unit aggregate

22 October 2026. Independent audit; no repository changes. Verdict: YES, the packed primitive and the antipodal unit-product theorem extend to an arbitrary odd character order m, restricting native tags to units. Choosing the auxiliary prime first removes the earlier near-linear auxiliary-supply caveat for THIS theorem. It does not repair the original difference/long-product acquisition gap, nor transfer prime-modulus quadratic-colour conclusions to composite m.

## Deterministic public supply

Put u=ceil(N^(1/6)). Choose the first prime ell≡3 mod4 with ell>2u, and set m=(ell−1)/2. Then m is odd, m≥u, ell=2m+1; no primality of m or Sophie Germain assertion is involved. Sieve successive doubled intervals (or sieve from 2 through successive doubled endpoints), recording primes and smallest prime factors. Fixed-modulus PNT implies ell=O(u), and therefore total sieve bit work soft O(u). All constants here are absolute.

For an explicit effective justification, Bennett–Martin–O'Bryant–Rechnitzer, *Explicit bounds for primes in arithmetic progressions*, Illinois J. Math. 62 (2018), 427–532, Theorem 1.2 with the uniform bounds (1.10)–(1.11), implies the weaker bound

    |theta(x;4,3)−x/2| < x/(160 log x), x≥8*10^9.

Consequently theta(2x;4,3)−theta(x;4,3)>x/2−2x/(160log(2x))−x/(160log x)>0. For u≥4*10^9 take x=2u and obtain ell≤4u. Below that fixed threshold there are finitely many inputs u; applying the same argument with x=8*10^9 supplies a universal constant-factor bound. The algorithm need not sieve to that huge threshold: it stops at the first actual prime above 2u. This is an asymptotic bit bound with an effective absolute constant, not a claim that these constants are practical.

Primary author-hosted full PDF opened and theorem/introduction inspected: https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf . Cached as EBPAP.pdf in this scratch directory, SHA256 958b0390475236b68afdec28ce006b1a1d6ac59484eea9443e0b287e9f61a541. Browser full-text reference turn864view0. No unproved RH assumption is needed for the stated result.

Factor the public m using the paid sieve and screen gcd(N,p) separately for EVERY distinct prime p dividing m, and also for the prime ell. On a composite semiprime input any nontrivial such gcd is a proper factor, even when the combined gcd(N,ell*m) would saturate at N. If no primewise screen finds a factor, gcd(N,ell*m)=1. Thus no combined-gcd saturation fallback or finite trial-division exception is required. Computing the separate gcds costs only polylogarithmically many O(log N)-bit operations.

## Character table and packed implementation audit

Factor ell−1=2m using the paid sieve's smallest-prime-factor table. Find a primitive root g modulo ell by testing candidates against every distinct prime divisor of ell−1. Even allowing ell candidates, each needs O(log ell) modular exponentiations with O(log ell)-bit exponents, so total work is soft O(ell), not an assumed least-primitive-root bound. Enumerate g^e for 0≤e<ell−1 and record e modm; this constructs the required character log table in soft O(ell). No discrete logarithm of an arbitrary given element or factor of N is used.

The reference PackedGauss constructor explicitly accepts every positive k dividing ell−1. Its projector(a) is

    E_a=(1/h) sum_(t=0)^(h−1) X^(a t), h=k/gcd(a,k).

At any character component it is one exactly when that component's a-th power is trivial, including proper-divisor character orders. Its product_constant uses both=E_a E_b and cancel=E_(a+b)−both, hence retains both-trivial and nontrivial-cancellation exceptions for composite k as well. Intermediate exponents in binary acquisition need not be units; these projectors are exactly what handles them. All h divide m and are units modulo N under the checked gcd condition. No factoring of m beyond the paid public sieve is needed by the arithmetic identities.

The current reference code uses trial division to factor public ell−1 and a trial primality test on ell; each costs only soft sqrt(ell) and is within the bound. Its primitive-root candidate search is also within soft ell by the worst-case count just given. Replacing those routines by the supplied sieve metadata simplifies bookkeeping but is not necessary for this aggregate's soft bound. Acquisition of a requested C_E takes O(log E) Jacobi histograms, each O(ell), and O(log E) quasi-linear cyclic convolutions of length m, with polylogarithmic N/ell bit overhead. Thus C_m and the constant number of required powers cost soft(ell+m)=soft u. Composite k does not create a hidden m-fold overhead.

## Exact aggregate extension and exceptions

Work in A=(Z/N)[X]/(X^m−1), m odd, gcd(N,ell*m)=1. Define E0=m^−1 sum X^r and D=E0+(1−E0)ell. Since X^m−1 is separable at both hidden primes, equality on all geometric character components proves equality in the whole local algebra and hence in A. E0 selects ONLY the trivial character even when m is composite.

For a unit tag j modm, raising a character of any order d|m to j preserves whether it is trivial. Every such character has chi(−1)=1 since d is odd. Therefore

    g_j g_-j=D,
    C_j C_-j=U/D, U=g_1^m=−C_m.

At nontrivial proper-divisor components the product is ell, not a new exception. At the trivial component it is 1. Restriction to unit tags is essential: for a nonunit j the trivializing projector can be larger than E0.

Take representatives j in (Z/m)^*, a_j=Nj^(−2) modm in [1,m−1]. They are units and satisfy a_-j=a_j as INTEGERS. Canonical b_j is the unique centered representative solving

    j m b_j = j² a_j−N mod m²,
    ell_j=m b_j−2a_j j.

This uses the inverse of j modulo m; no inverse of a nonunit is required. The antipodal congruence gives b_j+b_-j=2a_j−m s_j, with s_j∈{0,1,2}, so ell_j+ell_-j=−m²s_j exactly. There are h=phi(m)/2 unit antipodal pairs. With A=sum_pairs a_j and S=sum_pairs s_j,

    product_units C_j^a_j=(U/D)^A,
    T_j T_-j=U^(−m s_j)D^(a_j+N),
    product_units T_j=U^(−m S)D^(A+Nh).

The rho_j maps are automorphisms because j is a unit; N is a unit modulo m, so r_j=Nj^−1 is again a unit and pairs antipodally. The reciprocal quotient identity C_N bar(C_N)=D^(N−1) still holds on EVERY nontrivial component, including proper-divisor ones, and at the trivial component C_N(1)=1 for odd N. Hence the full prior proof is unchanged after replacing (m−1)/2 by phi(m)/2 and restricting every sum/product to unit tags. It is not legitimate to apply these formulas to all nonzero tags for composite m.

The three-vector shared pair representation and the whole-vector output retain soft u acquisition costs. Units, inverses, phi(m), all centered lifts and pair enumeration are paid using the public factor/sieve metadata in soft m work. Expanding every pair into a separate degree-m array remains quadratic output and is not claimed.

## Source and scope

If a hidden prime P has nonunit residue modm, then gcd(P,m)>1 and the prechecked gcd(N,m) reveals a proper factor in the admissible asymptotic regime. Otherwise its true tag is among the retained units. Thus restricting to unit tags does not silently delete a surviving true source. The full own-tag Frobenius identity is valid for a unit P modulo m and ell, regardless of primality of m.

This repairs the public auxiliary supply and metadata charge for the acquired unit aggregate, pair representation and normalization identities. It does NOT assert that composite m preserves the two prime-modulus Legendre masks or their common H reduction. It does not supply order/recovery of the new scalar ell or Gauss seed, acquire target-minus-seed products, or close the universal sixth-rate factoring goal.
