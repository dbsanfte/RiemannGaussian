# Independent review: exact LCM exponent shortcut

2026-10-15. Reviewed root's supplied theorem and proof. Verdict: valid with qualifications below; no general gcd-only lower bound follows.

## Actual-source bad tags

For common u=gamma^v, E_j=N+a_j+ell_j-m^2 kappa_j and k_i=E_j-v-m^2i, multiplication by j^2 modulo prime m gives
j^2 k_i=N(j-1)^2-vj^2.
The coefficient of j is -2N, nonzero for odd m coprime to N. This is a nonzero polynomial of degree at most two, so at most two nonzero tags satisfy m|k_i. The condition is independent of i. Every other tag has gcd(k_i,m^2)=1 for every i. This argument requires a common exponent origin v; arbitrary row-dependent origins v_j invalidate the polynomial root count. For J proportional to m, deleting two tags leaves long rows when those rows have the stated common length.

## Arithmetic progression lemma

For u_h=a+dh>0, 0<=h<n, with gcd(a,d)=1:

lcm(u_0,...,u_(n-1)) >= product_h u_h/(n-1)! >= a d^(n-1).

The valuation proof is correct. If p|d, no u_h is divisible by p. Otherwise choose j maximizing v_p(u_j). For i!=j, v_p(u_i)<=v_p(u_i-u_j)=v_p(d(i-j))=v_p(i-j), including the case of tied maximal valuations. Hence
v_p(product u_h)-max_h v_p(u_h) <= v_p(j!(n-1-j)!) <= v_p((n-1)!).
This proves the first inequality prime by prime. The second follows from u_h>=dh for h>=1, leaving u_0=a.

A nonzero signed AP of length L and step m^2 has at least ceil(L/2) entries of one sign. They form a contiguous segment of indices; reversing the negative segment makes their absolute values a positive AP of step m^2. Coprimality persists. The displayed bound therefore gives log_2 LCM >= (ceil(L/2)-1)2log_2 m. Zero exponents must be separated first; if any k_i=0, this nonzero-AP argument is not the relevant branch.

## Mandatory nonzero-output qualification

The claim about every common multiple must say every NONZERO integer common multiple K. K=0 is a common multiple but has no large bit length. With K!=0, |K|>=LCM, proving the bit-size bound.

An exact formal exponent chain beginning with exponents 1,-1,0 and allowing multiplication/inversion of the corresponding gamma powers has maximum exponent magnitude at most 2^t after t multiplications; inversions only negate exponents. Thus producing formal exponent exactly K requires t>=ceil(log_2 |K|). This is not a bound on producing an equal residue gamma^e=gamma^K by exploiting finite-order relations, nor on algorithms which do not construct this power.

## Collision equivalence

For squarefree N=pq and gamma having prime multiplicative order R_p and R_q in the two hidden fields, gamma^k_i-1 is zero in a hidden field exactly when its prime order divides k_i. A prime divides the LCM of the nonzero |k_i| exactly when it divides at least one k_i. Therefore taking K to be that LCM preserves the two field-zero indicators, and hence preserves gcd with squarefree N. Known unit factors in the original residuals do not affect the gcd.

If a local order is composite, it may divide the LCM without dividing any individual k_i; the exact equivalence fails and extra zeros may occur. For a merely arbitrary common multiple K, even prime local orders can acquire extra divisors: the equality statement requires K equal to the LCM, or another K with exactly the same relevant prime divisibility. For nonsquarefree N, field-zero indicators alone do not determine prime-power valuations of the gcd, so the squarefree hypothesis is material.

## Scope

This rigorously obstructs the exact nonzero common-multiple exponent construction on even a single admissible L=Theta(m^2) row. It does not obstruct finite-order reduction, another gcd-only scalar, symbolic exponent manipulations without constructing the power, or arbitrary implicit acquisition.

## Final durable report pin and source check

Reviewed exact durable report /home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-long-query-20261015/lcm-exponent-obstruction.md, SHA256 1bf802103017848348c51b43ea56cdedb6dbce9c3c60a525d1a3a1afea1d25a4. All qualifications above are incorporated; no correction requested.

Historical provenance verified against the restored candidate reports with their stated hashes. The current journal docs/semiprime-factorisation-investigation.md lines 28415--28420 records the square-class argument yielding a linear population of long first-current singleton queries. Lines 28685 onward supply the actual centered exponent formula and separation, and lines 28709 onward state Omega(m) long singleton lengths and a common start-zero top-bit group of Theta(m^2) length. The charged-acquisition audit JSON at lines 655, 662 and 1656 repeats the full signed-half length and population contracts. Consequently the report's use of at least one long tag after deleting at most two exceptions is supported by the historical source; it is not inferred merely from an arbitrary J-element target list. These references establish the retained historical claim, not a fresh audit of its upstream square-class proof.
