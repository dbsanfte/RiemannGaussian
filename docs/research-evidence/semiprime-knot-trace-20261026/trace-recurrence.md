# One common swap trace and additive stationary colours: executed recurrence and whole-query cost

26 October 2026. Bounded constructive pass; scratch only, no numerical campaign or repository edits. Read the prior skein-selector.md before using the pair identities: its pair-first/mixed-root decoder is OLD credit and is not re-proved as an advance here.

**Outcome.** The common A across the entire family really supplies every pair colour coefficient in soft k. The stronger stationary-colour proposal also gives an exact two-generator character and second-order line recurrence, with canonical q-carries explicit, for every one of soft-k total coloured incidences. These are actual finite identities, not a fake conic lift. They do not yet contract the complete long query. Fixed-centre Chebyshev strings are essentially absent in the actual catalogue; postponing trace specialization gives an ACTUAL expanded degree Omega(k²); and the additive coloured lattice is not closed under the native hyperbolic cutoff. The exact colour recurrence with its moving clock endpoints is recorded as the narrower remaining scalar problem. No improved full-query bound is proved.

## 1. Normalize all swap pairs with the SAME known A

Set

    A=beta^((N-1)/2), C=beta^((N+1)/2), Z=A+A^-1,
    s=a+b, d=a-b,
    u_(s,lambda)=C^s*beta^lambda.

All exponents are integers because N is odd; no unknown square root is adjoined. Then exactly

    beta^(a+bN+lambda)=u*A^-d,
    beta^(b+aN+lambda)=u*A^d.

Writing D_0(Z)=2,D_1(Z)=Z,D_(d+1)=Z D_d-D_(d-1), the pair quadratic is

    g_(s,d,lambda)(t)=t²-u D_d(Z)t+u².               (1)

D_-d=D_d. For every nonaxis native pair, |a|+|b|<=|ab|+1<=k, hence |s|,|d|<=k; the axes obey the same bounds. All D_0(Z),...,D_k(Z) are acquired in O(k) ring operations, then all actual u and g coefficients in soft J. This removes separate character powering per pair, but the existing exponent list already costs soft J to acquire. No long interaction is evaluated by this coefficient sharing.

No unit property of A-A^-1 or of D_d-D_e is inferred merely from beta's order: the known exponent (N-1)/2 can shrink its local orders. The displayed recurrence uses no such inverse and is valid even if these traces coincide. A separate needed nonunit test can factor through the existing short-label consumer; it is not assumed free.

For the normalized polynomial h_d(X)=X²-D_d(Z)X+1, the EXACT common-argument recurrence is

    h_(d+1)=Z h_d-h_(d-1)+(2-Z)(X²+1).               (2)

Equivalently it has a homogeneous three-state recurrence. Crucially X=t/u must be the SAME in (2). Actual centres vary with(s,lambda), so this is not already an advancement of all native pair values at one physical t.

## 2. Test the two obvious whole-family Chebyshev compressions

### Fixed centre does not supply a long native colour string

Suppose two actual rows have the same s and canonical lambda. Since lambda²=4Nab modulo H, their products satisfy S=H/4 divides ab-a'b', using gcd(N,S)=1. But |ab-a'b'|<2k<S for k>16. Hence ab=a'b', and their shared sum s determines the same unordered pair {a,b}. Thus each exact(s,lambda) centre has only one unordered swap pair.

The integer centre label s(N+1)/2+lambda is itself unique across distinct(s,lambda): a nonzero change of s changes it by at least(N+1)/2, exceeding the whole lambda width H. Accidental local equality of the beta-powered centres may occur; any needed separation has to be tested with the old derivative/short-label algorithm. It does not create an available known long colour string. Consequently the useful finite identity for a CONTIGUOUS d range at one centre,

    product_d h_d(X)=product_d(1-X A^d)(1-X A^-d),

does not group the actual acquired family into such strings for free.

### Expanded common-trace fusion has actual degree Omega(k²)

Freeze the acquired centre scalars u_j and regard Z as a formal trace. A product of NONDEGENERATE (d_j!=0) pair factors at a supplied unit t has Z-degree sum_j|d_j|, since each D_d is monic and its top coefficient in(1) is the unit -t*u_j. There is no cancellation at that top degree. A d=0 factor is independent of Z and may be nonunit; it must be handled by the inherited diagonal query, or omitted only after unit certification.

This sum is already Omega(k²) on an actual retained primitive subfamily: take b=1, k/2<=a<k with a odd and aN=1 modulo3. There are Theta(k) such a. Their unit quadratic congruences have native phase roots; a!=+/-b, so diagonal pruning does not remove them. Nonaxis integer-zero deletion removes none, and complete-swap/opposite folding only changes the count by a constant. Every d=a-1 has size Omega(k). Thus an expanded Chebyshev/colour coefficient list is too large even before inserting the long clock. Evaluating Z first avoids that expansion, but then gives exactly the already acquired ordinary degree-O(J) polynomial in t and the old norm query. This is a cost test of that expanded-fusion architecture, not a lower bound for algorithms using the scalar Z implicitly.

## 3. The genuinely additive native colour construction

The stationary-colour refinement is stronger than treating each lambda as an unrelated conic root. For every unit j modulo k choose its representative 0<j<k and its inverse j^-1 modulo H. Define the index-k lattice

    Lambda_j={(a,b): a*j²=b*N mod k},

and the EXACT linear lift and canonical phase

    mu_j(a,b)=-a*j-b*N*j^-1,
    lambda_j=mu_j-H*floor(mu_j/H).

On Lambda_j, aj-bN j^-1 is divisible by k, so

    lambda_j²-4abN=(aj-bN j^-1)²=0 modH.

Moreover lambda_j is independent of replacing j by any unit lift j+kt modulo H ON this lattice. Indeed f(x)=ax+bN/x satisfies

    f(j+kt)-f(j)=kt*(a-bN/[j(j+kt)])=0 modH,

because the bracket is divisible by k there. All inverses are only modulo the known H, where the arguments are certified units.

For the actual smaller or larger factor P with P=j modulo k, the same identity applies to f(P), so lambda_j=-(aP+bQ) modulo H. Therefore every old actual stationary witness appears in its physical unit colour. This is a COVERAGE proof for replacing the conic enumeration by the coloured one, provided the original bounds, axes, deletion and metadata are retained. It does not reveal the correct colour j from public N.

Swap exchanges colours by j -> N*j^-1 modulo k. Taking that lift modulo H makes the stationary phases identical for(a,b) and(b,a); canonical representatives give the same result by the lift-independence above. So swap-pair traces couple this explicit colour involution, rather than all belonging to one secretly known colour.

## 4. Pay for all colours and incidences

There are phi(k)=Theta(k) public colours. For fixed(a,b), put g=gcd(a,b,k). If a unit j solution exists, dividing by g gives unit a/g and b/g modulo k/g and at most a constant number of square roots modulo that 2-times-3-power modulus. Lifting j back modulo k gives O(g) solutions, filtered for gcd(j,k)=1. The number of pairs divisible by g with |ab|<k is O((k/g²)log k). Summing the resulting incidence bound over g|k gives

    O(k log k * sum_(g|k)1/g)=soft O(k),

because k has only the fixed prime support2,3. The four axes add O(k) colour incidences. The existing Hensel/root construction enumerates these incidences output-sensitively; canonical phases and original labels cost polylogarithmic work each. All unit j inverses and lattice bases also cost soft k total. No k-by-k colour/row table is acquired.

The acquisition algorithm is explicit. Enumerate positive |a| from1 to k-1 and positive |b| up to floor((k-1)/|a|), with the four sign choices, costing O(k log k) integer iterations. For each pair compute g and n=k/g. Reject it if a/g or b/g is not a unit modulo n; otherwise compute R_j=N*(b/g)*(a/g)^-1 modulo n. Solve j_0²=R_j modulo n using the known2-times-3-power factorization: direct parity modulo2 and the at-most-two unit roots modulo3 lifted by the invertible derivative2j_0 through its 3-powers. Enumerate j=j_0+t*n for0<=t<g, filtering gcd(j,k)=1. Each surviving j supplies its known inverse modulo H and the canonical lambda_j. The total O(g) lift enumeration over pairs is bounded by the same convergent sum above, including filtered lifts; it is not a scan of all k colours for each row. Handle n=1 directly if encountered. The four axes are generated by one enumeration of the unit j and their four explicit coefficient pairs, costing O(k). Deduplicate literal row triples if desired while retaining every colour and original swap label as metadata. Apply the old public deletions and unit-certified pruning with their existing survival proof. All integer operations have polylogarithmic cost. Thus the incidence bound is an actual soft-k enumeration algorithm, not an existential count.

A simple lattice basis is (k,0),(r_j,1), where r_j=N*j^-2 modulo k. Its determinant is k. The two unwrapped pair matrices at these basis vectors cost O(1) supplied-unit powers per colour, with O(log N)-bit exponents. Thus the entire two-generator input is genuinely paid in soft k, not a separate wide module for each colour. This is useful structure, but still preparation until its joint scalar is evaluated.

## 5. Exact carry-aware recurrence on each coloured lattice

For v=(a,b) in Lambda_j define the unwrapped diagonal matrix

    Mtilde_j(v)=diag(
       beta^[(1-j)a+N(1-j^-1)b],
       beta^[(N-j)a+(1-N*j^-1)b]).

This is an EXACT multiplicative character: Mtilde(v+w)=Mtilde(v)Mtilde(w). Its scalar entries, determinant and trace at any supplied integer combination of the two known lattice basis vectors are acquired by binary powering. They use no hidden factor or group logarithm.

Let tau_j(v)=floor(mu_j(v)/H). The native canonical pair matrix is

    M_j(v)=q^(-tau_j(v))*Mtilde_j(v).

Its diagonal entries are precisely the two original beta^E swap roots, with no dropped phase. For any v,w in the lattice put

    c_+=floor((lambda_j(v)+lambda_j(w))/H) in{0,1},
    c_-=floor((lambda_j(v)-lambda_j(w))/H) in{-1,0}.

Then

    M_j(v)M_j(w)=q^c_+ M_j(v+w),
    M_j(v)M_j(w)^-1=q^c_- M_j(v-w).

If T_j(v)=tr M_j(v), the exact determinant-weighted product-to-sum identity is

    T_j(v)T_j(w)
      =q^c_+ T_j(v+w)
        +det(M_j(w))*q^c_- T_j(v-w).                (3)

All carry coefficients are acquired units. This is the lawful coloured Chebyshev/skein relation; the linear phase DOES fix the earlier generic-conic additivity problem.

Along an affine lattice line v+n w, the unwrapped traces obey the initialized second-order recurrence

    Ttilde_(n+1)=tr(Mtilde(w))*Ttilde_n
                  -det(Mtilde(w))*Ttilde_(n-1).      (4)

Recovering native traces FROM the unwrapped traces inserts the known q^(-tau_n) at every step. Equation(4) costs O(log n) by two-by-two powering at a supplied n. It is not a recurrence for the PRODUCT of comparisons with all unknown physical clock indices.

## 6. Execute the native finite-support boundary test

The native support is the hyperbolic band0<|ab|<k with the specified axes, not the whole additive lattice. It is not closed under the vector additions in(3). For the actual primitive positive subfamily in Section2, v=(a,1) has |ab|>=k/2, while2v has |(2a)*2|>=2k and is OUTSIDE the catalogue. Thus already squaring these actual retained characters invokes an out-of-support colour state. Such boundary states are well-defined public powers; they are not automatically legal original comparison leaves or units at every physical clock.

Unwrapping lambda avoids the carry in the character recurrence but moves the comparison interval. Specifically

    beta^E-q^i=q^(-tau_j(v))
                  *[beta^Etilde-q^(i+tau_j(v))].     (5)

The row-dependent tau may be large; (5) is exact but does not give a common shortened physical interval. Using the original canonical interval keeps the carries explicitly. A root of an out-of-support boundary state or a newly shifted endpoint needs its own nonzero-gap/coverage proof; no original annihilator licence is inferred from the character identity.

A finite product along a whole lattice line, if its canonical centre were held fixed, could be expressed through Pochhammers at the line character eigenvalues. In the actual colour support, the hyperbolic cut and(5)'s stair-step endpoints remain. Even a perfect soft(J_j+sqrt m) scalar oracle PER colour would incur Theta(k)*sqrt m startup if used independently; grouping all incidences together recovers only the old soft(J+sqrt(Jm)) evaluator. Thus the needed gain is genuinely joint across colours or a proven thinner colour/witness selection, not coefficient acquisition in(4).

The lattice area has a potentially useful alignment: an ambient formal quantum torus with commutator beta^k restricts to commutator beta^(k*det basis)=q on Lambda_j. This may motivate a quantum-cluster/fan identity for these coloured polygons. But the acquired Mtilde characters commute; promoting them to q-commuting operators is additional data. Since q has large local order, no invertible rank-O(k) exact q-Weyl representation is supplied, as the preceding quantum-torus boundary audit shows. A physical open-clock realization must retain its boundary. No pentagon ratio or trace sum is identified with the desired multiplicative collision query without that scalar calculation.

## 7. Primary skein identity and final scalar obligation

Frohman–Gelca, *Skein Modules and the Noncommutative Torus*, Transactions AMS352(2000),4877–4888, Theorem1, https://arxiv.org/abs/math/9806107 and author PDF https://www.math.ttu.edu/~rgelca/torus6.pdf , supplies the Chebyshev-decorated product-to-sum formula. At commutative character specialization it is the trace identity used in(3). It controls a SUM of the two new slope states; it does not assert a product-of-all-slopes norm or select a finite physical interval. The pair-level realization/decoder in the old skein-selector report remains prior credit. No root-of-unity transparency theorem is invoked for the arithmetic A or q.

The explicit new arithmetic input is therefore the soft-k list of carry-aware additive stationary colours and its genuine two-generator recurrence(3),(4). A useful completion would contract the product of the native pair characteristic factors over their hyperbolic lattice bands and the long physical interval, jointly across those colours, without expanding the Omega(k²) common-trace polynomial or replacing(5) by a falsely common boundary. It could alternatively select a small set of colours/pairs with proved actual-factor coverage. Neither scalar theorem was obtained here.

Any nonunit of an ACTUAL retained comparison has the old proper-gcd or nonzero short signed-gap consumer. Additive trace zeros, out-of-band character states and new interval endpoints do not acquire that decoder merely by(3). Existing complete data still feed the common-base query at soft(J+sqrt(Jm)); no new factoring exponent is claimed. The full sixth-exponent goal remains open.
