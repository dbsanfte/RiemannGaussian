# Independent review: selected q-binomial coefficient primitive

2026-10-15. Verdict: PASS. No substantive correction requested. This is a positive conditional subroutine review, not a claim that the original long target-product query is acquired.

Reviewed literature/selected-qbinomial-primitive.md SHA256 78b387b6cf64cba8a358a8a796ede8f1640dc5effc36882dc484a99935f95ddb.

## Shared block acquisition

The cleared coefficient recurrence has the correct sign: (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k. Its numerator and denominator prefix products U,V give c_k exactly for 0<=k<=L under the stated parameter-unit hypothesis. At k=L, U_L uses i<L only, so it does not accidentally include the next-step zero factor q^L-q^L. All used numerator factors are also units under the hypothesis, though no numerator inverse is required.

For b=ceil(sqrt L), evaluating A_b at t=0,...,floor(L/b)-1 supplies every complete block prefix needed at a=b floor(k/b), including k=L when L is divisible by b. The degree-b block can be constructed by geometric doubling in soft O(b). Unit-q chirp convolution evaluates the O(b) block points without interpolation or root-of-unity assumptions. Cumulative multiplication then acquires all shared starting prefixes at the claimed cost.

## Arbitrary tails and repeated nodes

Every tail k-a is less than b, so descending binary refinement only requires power-of-two polynomials A_ell with ell<b. The total of these degrees is O(b), and their doubling construction is soft O(b). At one level monic product/remainder trees evaluate the degree-ell polynomial at nu current nodes in soft O(nu+ell) arithmetic. Repeated points and nonunit pair differences are harmless: the method divides by monic polynomials only, rather than inverting node differences.

Using a level value only when its bit is set and then increasing a by ell covers each original prefix exactly. The identity A_ell(q^a)=prod_(i=a)^(a+ell-1)A(q^i) gives the correct segment. Summing the O(log b) levels yields soft O(nu+b), including nu>b; there is no hidden requirement that nu<=sqrt L. Zero tails and k=0 require no segment. The two streams may be processed separately with only a constant factor.

## Units, bit cost and memory

Every V value is a unit. A product/batch inversion uses one extended-gcd inverse of their combined product plus O(nu) ring multiplications. This does not invert c_k, a potentially zero target value or any collision residual. The report correctly distinguishes a proper gcd from gcd=N if the parameter-unit premise is absent; that fallback alone would not justify an unconditional algorithm for arbitrary q.

All powers q^L, q^a and u^k are powers of supplied units and can be acquired within O((b+nu)log(L+1)) elementary ring operations, absorbed by soft notation. Fast polynomial products over Z/N can be implemented through integer convolution/Kronecker encoding without supplied finite-ring FFT roots. In the stated polynomial-size-index regime, ring elements and input indices have polylogarithmic bit size, giving the claimed soft O((sqrt L+nu)log N) bit bound with the normal logarithmic overhead. Sequential refinement permits soft O(b+nu) residue storage; the retained block polynomials have total degree O(b), and one multipoint tree at a time fits the same soft storage bound.

These are conditional algorithmic upper bounds with all preprocessing included, not merely counts of output values. No numerical hidden order is an algorithm input.

## Actual source and scope

For actual q=gamma^(m^2) with retained local prime orders exceeding 16m^2, and L<=4m^2, each 1-q^a for 1<=a<=L is nonzero in both hidden fields. Thus the parameter-unit premise is valid on that qualified source. The report explicitly does not assign it to arbitrary q or every routing branch.

Selected indices can depend on the full public N because this algorithm is valid for every supplied list, not merely a catalog-based counterfamily claim. Repeated indices can share output or remain in the monic evaluation lists. The primitive handles ONE coefficient stream, with common q,L,u; its shared block acquisition is therefore legitimate. It does not justify batching distinct row products P_L(z_j) as if each were one selected coefficient.

Origin/start or interval-length changes in an outer certificate simply require a new permitted invocation with its corresponding parameters, and the report charges that invocation. This compatibility does not supply the still-unproved rational reduction, residue/pole coefficients, discrete-log positions, parameter derivatives or analytic continuation values. In particular no fast formal weighted sum or changing-target long-query algorithm follows from selected coefficient acquisition alone.

The primary q-holonomic several-index theorem is appropriate provenance, but the composite-ring extension here is independently supported by the explicit shared-block/monic-tail construction rather than an unexamined field-interpolation transfer. No broader literature-completeness claim is inferred.

No blocker was found. The primitive is a genuine paid positive partial interface with cost soft O(sqrt L+nu), while the canonical long-product acquisition remains open.
