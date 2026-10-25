# Fermat-quotient cover: exact consumer and remaining target

22 October 2026. Independent scratch derivation. No repository edits, build, or coverage campaign. This gives a constructive consumer for the proposed cover, with its actual cost; it does not give the requested soft-O(r) consumer or a new factorization exponent. The balanced linear construction is recorded separately from the rank-three quadratic construction and is not promoted to an unbalanced-case theorem.

## 1. Cover construction independently checked

Let r be an odd prime, H=r^2, gcd(r,N)=1, and q_r(x)=(x^(r−1)−1)/r mod r for units x modulo H. Set Q={q_r(c):1<=c<r} and retain one representative c(q) for every q in Q.

Primary source: Ostafe–Shparlinski, [Pseudorandomness and Dynamics of Fermat Quotients, arXiv:1001.1504v2](https://arxiv.org/pdf/1001.1504v2), Theorem10, printed p.13, gives |Q|>=(1+o(1))r/(log r)^2. Its identities(6)–(7), printed p.7, give q_r(xy)=q_r(x)+q_r(y) and the additive-lift rule. These primary statements were checked; no distribution heuristic is used.

Here is the exact deterministic greedy cover. For currently uncovered U subset F_r, compute

    C(tau)=sum_(q in Q) 1_U(tau−q).

The average is |U||Q|/r. Choose a maximizing tau, add it to A, and remove tau−Q from U. Each iteration leaves at most |U|(1−|Q|/r) uncovered points. Thus at most ceil((r/|Q|)log r)+1=O(log^3 r) iterations suffice. These are integer cyclic convolutions of two 0/1 arrays, with coefficients at most r; exact Kronecker integer convolution or exact fast polynomial multiplication computes each in soft O(r) bit work. Scanning and updating the labels also costs soft O(r) per iteration. Computing all Fermat quotients by modular powers first costs soft O(r). Overall this is soft O(r), with ordinary polylogarithmic factors charged.

For each newly covered v=tau−q, store the label (tau,c(q)). This proves A−Q=F_r and supplies explicit witnesses for every field element v. A maximizing tau cannot be a previously chosen one while U is nonempty, since its translate has already been removed.

Define the canonical integer catalog, with representatives in [1,H),

    S={j^r(1−r tau) mod H: 1<=j<r, tau in A}.

Its elements are distinct across (j,tau): their residue modulo r is j and their Fermat quotient is tau. Hence |S|=(r−1)|A|=soft O(r), and it is acquired in soft O(r) bits.

For ANY integer P coprime to r, let v=q_r(P) and take its stored label (tau,c). Then q_r(cP)=tau. The element j^r has residue j modulo r and Fermat quotient zero; q_r(1−r tau)=tau. These two invariants determine a unit modulo H uniquely. Therefore, for j=cP mod r,

    cP = s mod H for the catalog element s=j^r(1−r tau).

This coverage proof does not compute the unknown q_r(P), and does not presume the consumer knows c. It is a valid existence-and-public-catalog theorem for every P. If r divides N, gcd(r,N) handles that case before this construction.

## 2. A complete direct integer-progression consumer

This consumer bypasses all exponent/order issues. Put Pmax=floor(sqrt N), M=(r−1)Pmax, and

    L=floor(M/H)+1.

For the covered multiplier, 1<=c<r and P<=Pmax give 0<cP<=M and

    cP=s+Hh,  0<=h<L.

Thus the exact integer product

    Z=product_(s in S) product_(0<=h<L) (s+Hh) mod N

has a nonunit gcd with N. It uses the original positive multiples, with no CT or character-support substitution.

Let J=|S|. Choose an integer block size d about sqrt(JL), capped at L if necessary. Form

    F(Y)=product_(0<=i<d) (Y+Hi) in (Z/NZ)[Y].

For every full block k and every row s, evaluate F(s+Hd k). There are K=J floor(L/d) such nodes. Monic product/remainder trees evaluate them in soft O(d+K) ring work over Z/NZ; distinct or unit-separated nodes are not required. No modular inversion is needed. The common final partial block is handled by its own degree<d polynomial at J nodes. Multiplying the acquired block values therefore costs

    soft O(d+JL/d+J)=soft O(sqrt(JL)+J).

All coefficients, evaluation nodes and integer exponents have O(log N) bits in the stated range. The corresponding bit cost is the same soft bound, suppressing the usual logarithmic arithmetic factors. For r~N^(1/6), J=soft O(r), L=O(r^2), this is soft O(r^(3/2))=soft O(N^(1/4)). This is an actual applicable consumer, but it does not improve the stronger existing one-fifth frontier.

**Saturation is recoverable.** Require the public bound M+H<N; it holds for all sufficiently large N when r is within a fixed factor of N^(1/6), with the finite remaining range handled directly. Then every included leaf integer s+Hh lies strictly between 0 and N. If gcd(Z,N) is proper, return it. If it is N, descend a product tree over the acquired block values: discard a unit child, return a proper gcd, or retain a child with gcd N. At a saturated block, compute/descend its at-most-d integer factors in soft O(d) additional work. A leaf cannot be divisible by N because it is positive and below N. Consequently a nonunit leaf has a proper gcd, and descent must yield a factor. Products containing different P- and Q-multiples are therefore safe; the algorithm never reports saturation alone as factor recovery. The localization cost is absorbed in soft O(d+K).

## 3. Balanced linear giant refinement independently derived

For every s in S choose the centered integer b_s satisfying

    b_s = −N/s mod H,  |b_s|<=H/2,
    d_s=(N+s b_s)/H,
    g_s(h)=b_s h+d_s.

These rows are acquired in soft O(J) bits. At a covered point cP=s+Hh, N=P Q,

    g_s(h)=P(b_s c+Q)/H = sigma P,
    H sigma=b_s c+Q.

Thus sigma is an integer. In a fixed balanced range P,Q=O(r^3), its absolute value is O(r), since |b_s c|<=O(r^3) and H=r^2. For any supplied unit beta, Fermat gives

    beta^(b_s c+N) = (beta^H)^sigma mod P.

This removes the quadratic multiplier phase in the balanced case. Its remaining all-input query has J rows and r possible multipliers c; acquiring those targets separately costs soft O(r^2). It is not enough to say that each individual exponent is linear.

The Fermat-quotient structure is exact:

    q_r(b_s)=q_r(−N)−q_r(s)=q_r(−N)−tau.

Hence the b catalog consists of O(log^3 r) quotient layers. Also q_r(N)=q_r(P)+q_r(Q). These identities do not supply the individual unknown q_r(P), q_r(Q), or the required c label. No soft-O(r) shared bilinear-phase collision evaluator was constructed here. In an unbalanced range Q/H may exceed O(r); that case needs its own coefficient/quotient analysis rather than importing the balanced bound.

## Constructive scope

The cover and its labels are rigorously acquired in soft O(r), and an exact localization-safe progression-product consumer is supplied at soft O(r^(3/2)) for the target parameters. The balanced linear rows further simplify the proposed giant surface, but their r-by-r phase contraction remains unacquired. These are explicit constructions and cost ledgers, not a generic obstruction or a new sixth-rate algorithm. The separate quadratic rank-three consumer and its full bit/order/recovery proof are not replaced by the balanced linear observation.

## Independent review of the companion cover theorem

After writing this report, reviewed `fermat-multiplier-cover.md`. Its q_r(0) domain correction, greedy cyclic convolution, witness partition, Teichmuller signs, distinctness, and all-unit coverage pass independently. The exact labeled bijection with H−r=r(r−1) units is correct. The rank-three construction's second-minimum argument is also valid: a shortest LLL vector parallel to the primitive Hx+s has norm at least its norm; LLL approximation then lower-bounds lambda1, and Minkowski plus lambda3>=lambda2 bounds lambda2. No assumption that the known linear vector is actually shortest is needed. Its small arithmetic sanity checks are not used here as a coverage proof. No implementation was reviewed in this pass.
