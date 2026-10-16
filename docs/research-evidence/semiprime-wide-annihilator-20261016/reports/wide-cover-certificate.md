# Arbitrarily wide explicit local carrier covers are sufficient factor certificates

2026-10-16. Conditional classical reduction on the inherited qualified source. Relative origins, assignments and positions may depend on the ENTIRE input; no low-digit prescription or origin-span bound remains. This does not acquire a cover, improve the existing direct long-query clock, or establish an all-input/Lean sixth-rate factorizer.

## 1. Exact source and certificate contract

Let N=P Q be in the same balanced, order-qualified actual family, with distinct odd primes P,Q=Theta(m³), m an odd current auxiliary prime, and m=Theta(N^(1/6)). The literal public unit gamma has distinct odd prime local orders R_P,R_Q>16m². Write

 P−1=vR_P, Q−1=wR_Q, 1<=v,w<m.                                      (1)

The stronger inherited bounds R_P>P^.677, R_Q>Q^.677 imply the last inequalities eventually; they are not asserted for arbitrary public units. Let D=R_P R_Q be gamma's exact global order. The factors, orders, v,w are proof-side premises, not algorithm inputs.

Use canonical first-current offsets

 a_j=N j^(-2) mod m, 1<=a_j<m,
 D_j=(N-a_j j²)/m,
 b_j=centered(m,-j^(-1)D_j),
 delta_j=a_j+m b_j−2a_jj, 1<=j<m.

The preceding native-center theorem supplies a deterministically computable light-tag set of size at least 2m/3, with labeled raw congruence energy

 #{delta_1+delta_2=delta_3+delta_4 modulo m²}<=E_*,
 E_*=m^.04 C_m^4 m^(5/2), C_m=64(floor(log₂m)+1)^4.                    (2)

This is the same retained majority family, at CURRENT candidates only. Its exceptions were already counted before choosing the cover. No extra exception deletion is introduced here. The first-current witness belongs to the full light catalog because every native publicPairs stream contains (a_j,1). The inherited nearlinear source setup computes the literal offsets and light tags.

The supplied certificate consists of an EXPLICIT relative-origin list kappa_j, carrier assignment i(j), positions 0<=s_j<T_{i(j)}, and listed lengths T_i. For fixed constants A,C require

 sum_j bitlen(kappa_j)<=C m(log m)^A,
 k²T<=m(log m)^A, T=sum_i T_i,                                      (3)

where k counts nonempty assigned carriers. Indices/group names may be canonicalized; their encodings take soft O(m) bits because every s_j<T and T is nearlinear. The metadata may depend arbitrarily on N, on previous observations, or on the hidden factors. This is not a static-plan theorem.

An arbitrary common origin c may be added to every kappa_j. It need not have short encoding or be supplied to the algorithm: it multiplies all nodes by the same unit and can be absorbed in the carrier seeds. Thus only relative origins are charged in (3). Put d=m² and consider nodes

 x_j=gamma^(-N-delta_j+d kappa_j).

The success promise is only that, in AT LEAST ONE of the two hidden fields, there exist unit seeds/ratios c_i,rho_i satisfying

 x_j=c_i rho_i^(s_j) for every tag j.                                (4)

These seeds/ratios need not be known, supplied, or identical in the two fields. They may be fully advised and outside the gamma subgroup. A global cover is a sufficient special case. A cover of the full family necessarily covers the proof witness below; no useful collision after trimming or reorigining is claimed.

## 2. Keep a short-origin witness and eliminate its carrier parameters

Discard any tag with bitlen(kappa_j)>(log m)^(A+2). At most C m/(log m)² tags are discarded. Intersect with the light tags, retaining at least g>=m/2 labeled entries eventually. Every origin used below has polylogarithmic bit length. The witness can depend on the full input and certificate; no counting argument requires it to be prescribed by low digits.

Set f_j=−delta_j+d kappa_j. Within each assigned carrier choose one base tag 0. Equal positions s_j=s_0 give candidate f_j−f_0. If a distinct position exists choose one tag 1 with s_1!=s_0 and also form

 K_j=(s_1−s_0)(f_j−f_0)−(s_j−s_0)(f_1−f_0).                          (5)

There are O(m) candidates, all of polylogarithmic bit length. Select the first nonzero integer K. Such a candidate MUST exist on the qualified energy family: otherwise each carrier's f values are rational-affine in its positions, with equal labels giving equal values. Weighted Cauchy--Schwarz/Hölder then gives

 E_integer>=g⁴/(2k²T).

But integer f-sum equality implies the delta congruence in (2), independently of origin sizes, so E_integer<=E_*. Equations (2)–(3) contradict this for sufficiently large m, since g>=m/2 and g⁴/(2E_*) is m^1.46 divided by a fixed polylogarithm. Repeated target values retain their source multiplicity; no distinct-node bound is needed.

In any field where (4) holds, equal-position subtraction or cross-power cancellation in (5) proves gamma^K=1. The common −N cancels, and carrier seeds and ratios disappear. Compute

 G=gcd(N,gamma^K−1).

Negative K is handled using the known unit inverse. A valid local cover gives G>1. If 1<G<N, return the proper factor. If G=N, K is a NONZERO global annihilator, so D divides K. Its absolute magnitude and quotient |K|/D may be arbitrarily large; only log|K| is polylogarithmic.

## 3. Classical extraction from an arbitrary polylog-bit global annihilator

The separate wide-annihilator extractor has the following precise interface: under (1) and balanced P,Q, a given nonzero global annihilator K of polylogarithmic bit length suffices for deterministic factoring in

 soft O(N^(5/32)+N^(5/64) sqrt(m)+sqrt(m))
     =soft O(N^(31/192))=soft O(m).                                  (6)

No factorization of K, no knowledge of D, and no bound |K|/D<=m² is supplied. This is a classical analytic/algebraic lemma, not a Lean theorem. Its mechanism and analytic premise are recorded here to make the interface unambiguous.

Remove only the power of two from |K|, obtaining K_odd. For any unit a, b=a^(K_odd) has local orders at most v,w<m: the odd R_P,R_Q factors are removed, while odd powering preserves the 2-adic parts of the orders of a. A composite-safe short-order separator costs soft O(sqrt(m)) and returns either a proper factor or the exact common local order of b. One construction finds the first nonunit prefix product product_(1<=i<=n)(b^i−1) by binary search. Its first leaf is min(ord_P b,ord_Q b); a saturated leaf certifies that these local orders are equal. Block polynomials and monic multipoint evaluation acquire each prefix in soft O(sqrt(m)), even with repeated nodes or zero divisors.

For phase one, scan integers a for Jacobi(a/N)=−1, returning a gcd factor immediately if found. The least such integer is at most N^(5/32) eventually. Run the separator on this ONE base after K_odd powering. If it reports equal local orders, the valuations s_P=nu_2(P−1),s_Q=nu_2(Q−1) must differ: for equal valuations, opposite Legendre symbols force different 2-adic order parts.

For phase two, scan all a up to N^(5/64), using the separator for each. The unknown field with larger s has a quadratic nonresidue within this range eventually, because its prime is O(sqrt(N)). That base has order 2-part exactly 2^s in the larger-s field and at most the smaller 2-part in the other, so its local orders differ and the separator returns a factor. Both scans are deterministic and use only public modular arithmetic, gcds, and Jacobi symbols.

The analytic premise is Lau--Wu, Theorem 1, in the pinned author primary preprint On the least quadratic non-residue. For every nonprincipal character modulo a cubefree q it gives least n with chi(n) not in {0,1} bounded by O_epsilon(q^(1/(4sqrt(e))+epsilon)). The Jacobi character modulo the distinct odd semiprime N is nonprincipal, and N is squarefree; the prime-field character is covered as well. Since 1/(4sqrt(e))<5/32, the fixed exponent slack absorbs the implied constant for sufficiently large inputs. This uses no GRH or quasi-RH premise. Bounded initial inputs can be handled by finite trial division. The arithmetic exponents satisfy 5/32<31/192<1/6.

## 4. Charged reduction and exact remaining acquisition gap

Reading the total explicit relative-origin metadata, computing the inherited source witness, trimming, and generating the O(m) candidates costs soft O(m) bits. The chosen candidate is short even if a few unused origins are huge. One modular power and gcd have polylogarithmic bit cost; in the saturated case apply (6). Carrier seed/ratio values and an arbitrary common origin never need to be read or acquired.

Therefore any supplied compressed cover satisfying (3)–(4) is a sufficient factor certificate in soft O(m) bit cost on the qualified family. It need only exist locally in one hidden field. There is NO numerical origin-span bound, no small-multiple cofactor bound, and no new deletion depending on the certificate or cover policy. Invalid supplied metadata may cause failure; a returned factor can always be checked by integer multiplication.

The missing work is acquiring such relative origins, assignments and positions. The reduction does not obtain them. It does not infer runtime hardness from the representation, nor exclude succinct programs, non-cover scalar observables, or another paid factor query. The direct long-row norm still has its previous general clock. The promised branch is a retained qualified family; a complete all-semiprime controller and Lean bit theorem remain unpaid.

## 5. Converse on this source: factors give a one-point global cover

Knowing P,Q suffices to construct a certificate in soft O(m) bits. Compute phi=(P−1)(Q−1). By (1), v,w<m, the prime m divides neither v nor w, and R_P,R_Q>m² are different from m. Thus gcd(d,phi)=1. Obtain eta=d^(-1) modulo phi and set

 kappa_j=eta*(N+delta_j) modulo phi, 0<=kappa_j<phi.

Then −N−delta_j+d kappa_j is divisible by phi. Euler's theorem for the known unit gamma gives x_j=1 globally for EVERY tag. Assign all tags position zero in one length-one carrier. Here k²T=1 and the total explicit origin encoding is O(m log N), satisfying (3). The source offsets, one modular inverse, and m modular multiplications are all paid at soft O(m) bit cost. No local order is needed for this construction.

Thus acquisition of an explicit cover of this class and factoring reduce to each other on the qualified source, up to soft O(m) work. This is a conditional information-preserving interface, not a logical or computational lower bound. Reorigining has changed the search intervals; the one-point construction does not claim collision coverage for the original interval query. In particular it does not make the cover a free N-only object.

Exact source and primary pins are in wide-cover-source-pins.json. The inherited energy/tag/encoding arguments are credited to the preceding representative-carrier and native-center reports. The arbitrary-annihilator extractor is the new conditional prerequisite summarized above; its final standalone report may be independently pinned alongside this bridge. No native edits, new Lean declarations, or numerical examples are used.
