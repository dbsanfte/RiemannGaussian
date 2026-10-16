# Literal-source countermodel: every scalar spectral test is a unit despite actual collisions

2026-10-16. Exact finite counterproof to a universal collision-forces-spectral-nonunit assertion, strengthened by whole-orbit and all-scalar Frobenius Bézout identities. This is not an infinite input family, an asymptotic avoidance theorem, or an operation lower bound. It does not refute a statement restricted to an unspecified sufficiently-large threshold. No prior packet is changed.

## One actual input and its exact public projection

    m=43, P=69263, Q=70163, N=4859699869,
    R_P=34631, R_Q=35081,
    L=2m²+2=3700,
    gamma=3896048378 mod N,
    q=gamma^(m²)=1007400003 mod N.

The five integers m,P,Q,R_P,R_Q are primes, verified by exhaustive integer trial division through their square roots. P-1=2R_P and Q-1=2R_Q, with distinct large primes and cofactors 2<m. Each R>16m²=29584 and R_P>P^.677, R_Q>Q^.677 (the latter inequalities are checked as exact integer-power inequalities). Cross-period exclusions hold, and P,P-1,Q,Q-1 are units modulo m². Both factors lie between 41³ and 43³ and have ratio below 3/2. Also

    41^6 < N <=42^6 <43^6.

The literal sixth width is B=42; the least prime >=B is m=43. Thus this is the actual first selector candidate, not a substituted modulus. The first-K menu bound floor(B^.020)=1 admits it.

Gamma is the SPECIFIC actual public base-2 projection, not an arbitrary CRT-selected generator:

    gamma=(2^(N-1))^((43!)^ceil(log2(N+1))) mod N,
    ceil(log2(N+1))=33.

The verifier computes this expression literally using modular exponentiation, without a hidden-order input. In each field, gamma^R=1 and gamma!=1. Since R is prime, the local orders are EXACTLY R_P,R_Q. CRT gives exact global order

    D=R_P R_Q=1214890111 >16m^4.

Because gcd(m²,R_P R_Q)=1, q has the same exact local orders. The hidden primes/orders are proof witnesses only. This witness satisfies the explicit numerical projected-large-order promises; it is not claimed to survive every unrelated historical exceptional-input deletion.

## Entire literal catalog and spectral polynomial

For all 42 tags 1<=j<43 use exactly

    I_j=j^-1 mod43,
    a_j=N I_j² mod43 in {1,...,42},
    D_j=(N-a_j j²)/43,
    b_j=centered(-I_j D_j mod43),
    delta_j=a_j+43b_j-2a_jj,
    z_j=gamma^(-N-delta_j).

Both source integer divisions are checked, and every delta lies in [-3m²,m²]. ALL 42 offsets and nodes are distinct. Every node difference is a unit modulo N, so this also lies on the actual unit-difference interpolation branch. Let

    H(t)=prod_(j=1)^42(t-z_j)=sum_(k=0)^42 h_k t^k, h_42=1,
    a=q^L,
    phi(X)=sum_(k=0)^42 h_k prod_(s<k)(1-Xq^s)
                               prod_(k<=s<42)(a-Xq^s).

These are the actual source nodes and the exact frozen spectral determinant, not independently chosen field coefficients. All offsets and H coefficients modulo N appear in certificate.json. The usual complete-block schedule has T=floor((L+1)/42)=88 tests X_n=q^(42n), 0<=n<88. The normalization value is

    phi(0)=4699488932 mod N, gcd(phi(0),N)=1.

Every scheduled value is a unit. The next section proves a much stronger statement with a finite algebraic certificate.

## Whole-orbit Bézout counterproof, not evidence from finitely many tests

Write phi_p for phi reduced modulo p. In EACH hidden field independently, compute

    r_p(X) = X^(R_p)-1 mod phi_p(X).

Both phi_p have degree 42. The retained certificate supplies polynomials A_p,B_p of degrees at most 41 such that the following EXACT identities hold in F_p[X]:

    A_p(X) phi_p(X)+B_p(X) r_p(X)=1,   p=P and p=Q.          (1)

`orbit.py` recomputes phi_p from the actual H coefficients, forms r_p by repeated modular squaring, performs polynomial extended Euclid, and verifies (1) by full coefficient equality. Independently, it constructs the actual companion matrix M and the pencil (I-aM)-X diag(q^s)(I-M), computes its determinant by prime-field Gaussian elimination at ALL 43 distinct arguments X=0,...,42, and compares against phi_p. Both sides have degree at most 42 and p>42, so this checks the entire determinant polynomial, rather than merely mirroring a possible coefficient-formula typo. Its arithmetic is ordinary integer modular arithmetic with elementary polynomial operations. The complete phi_p,r_p,A_p,B_p coefficient vectors are in orbit-certificate.json. In particular

    gcd(phi_P,X^34631-1)=1,
    gcd(phi_Q,X^35081-1)=1.                                (2)

For ANY integer v, the value x=q^v modulo p satisfies x^R_p=1. Since X^R_p-1-r_p is divisible by phi_p, a hypothetical phi_p(x)=0 would force r_p(x)=0, contradicting (1). Thus

    gcd(phi(q^v),N)=1 for EVERY integer v, positive or negative.  (3)

This proves failure not only of the 88 paid complete-block tests but of EVERY possible schedule consisting of evaluations of THIS same spectral polynomial at powers of THIS q, even with private index advice or unbounded indices. The conclusion follows from two short polynomial identities and exact local orders; it is not an inference from sampling all/most powers. Phi(0) is unit separately. At this stage (3) concerns the q subgroup; the next section strengthens it to every scalar argument. Different spectral polynomials or different determinant deformations remain outside the conclusion.

## Stronger: Frobenius Bézout identities exclude EVERY scalar spectral argument

For the SAME input and SAME phi, form the reduced Frobenius polynomials

    f_p(X)=X^p-X mod phi_p(X), p=P,Q.

The additional scalar-certificate.json gives exact coefficient vectors C_p,E_p with

    C_p(X) phi_p(X)+E_p(X) f_p(X)=1.                         (4)

`scalar.py` recomputes the modular powers and verifies these identities by full polynomial coefficient equality. It imports `orbit.py`, which also rechecks the direct companion determinants and the preceding orbit certificates. Both prime-field gcds are exactly one:

    gcd(phi_P,X^69263-X)=1,
    gcd(phi_Q,X^70163-X)=1.                                 (5)

Every scalar x in F_p satisfies x^p-x=0 by the finite-field Frobenius identity. A root of phi_p would therefore also be a root of f_p, contradicting (4). Consequently phi_p has NO root in its entire base field. CRT now proves the stronger conclusion

    gcd(phi(x),N)=1 for EVERY scalar x in Z/NZ.              (6)

Thus input-dependent arguments, advised arguments, cosets outside the q subgroup, and arbitrary scalar evaluation schedules cannot make THIS spectral polynomial reveal a factor on this actual input. This conclusion does not require enumerating the fields or the N residue classes: two degree-at-most-41 Bézout multiplier pairs and two reduced modular powers certify it. The earlier whole-orbit certificates are retained separately and unchanged. The all-scalar strengthening was co-derived by the root agent on the same witness and independently regenerated here; it is not a new input search.

## Actual row collisions remain, in both fields

The exact local canonical leaf-hit lists (tag,index), 0<=i<3700, are:

    P-field: (6,281), (13,2023), (33,1535), (39,186).
    Q-field: (6,2162), (8,208), (16,2674), (17,2086),
             (30,568), (36,2522), (39,1212).

In particular P mod43=33 has native own index 1535 and slope 40; Q mod43=30 has native own index 568 and slope 14. The verifier checks the exact source numerator divisibility and bounds for both own witnesses. A complete finite local q-power table additionally verifies the displayed hit lists. Therefore

    prod_(j=1)^42 P_3700(z_j;q)=0 mod P and mod Q,
    hence the original scalar norm is 0 mod N.

There are also proper single-field leaf hits, for example tag 33 in P and tag 30 in Q. Thus the original covered query really has factor information, while (3) makes every q-power spectral test a unit. No generic interpolation-node choices or surrogate low-digit lifts enter this counterproof.

## Verification and precise conclusion

Run `python3 verify.py`, then `python3 orbit.py`, and then `python3 scalar.py` from this directory. All three use only Python standard-library exact integer arithmetic and deterministic polynomial operations. The first regenerates certificate.json from the four displayed inputs m,P,Q,N and the literal source definitions; the second regenerates the two whole-orbit Bézout certificates. The modular inversion in polynomial Euclid is over the two explicitly certified prime fields, strictly proof-side. No field/order oracle is being granted to a prospective factoring algorithm.

The exact witness refutes the universal implication under these explicit finite hypotheses: “actual canonical row collisions force phi(x) to be a nonunit for some scalar x modulo N.” It leaves open an infinite actual-source avoidance family, any theorem explicitly restricted to all sufficiently large inputs, other spectral polynomials or determinant constructions, and the main restriction-stable nearlinear factor-query acquisition. It proves neither a lower bound nor a whole-query algorithm, and makes no claim of a new compiled Lean theorem.

The frozen spectral report supplies the determinant identity and interpretation; the full-Euclid report supplies the SPECIFIC public projection and qualified-order provenance; native files supply literal row/offset definitions. Exact hashes are in source-pins.json. Those definitions are inherited and evaluated here, not altered. The certificate is a finite counterproof, not numerical evidence for an asymptotic claim.
