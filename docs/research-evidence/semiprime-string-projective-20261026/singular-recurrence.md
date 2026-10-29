# Singular slice acquisition: linear precision and an output-sensitive alternative

26 October 2026. Scratch paper derivation; no tests, implementation or repository changes. **No improvement in the complete factoring exponent.** Two initialized algorithms below improve the overhead for acquiring the OLD full reciprocal-gcd output. One nonunit path already factors at the old scalar-query bound, independently of the number of hits; neither refinement improves that factoring bound.

Inputs: native-boundary packet finite-weighting.md, its corrected review, and the prior journal's gradient identities at lines 42602–42640 and channel/desingularization audit at lines 30790ff. These are old gradient/gcd targets and old backend algorithms, not new acquired invariants. The new point here is an explicit all-hit Hasse/gradient identity with composite-ring-safe execution and an output-sensitive comparison.

## 1. Actual prepared input, without extra roughness

Let y_1,...,y_J be the acquired native row roots, retaining actual signed/axis source maps and original clock x_i=q^(L+i), 0<=i<h. Use the existing exact-label deduplication and paid derivative/alias guard. On continuation y_j-y_l and x_i-x_t are units for unequal indices. A guard failure takes its existing proper-factor or nonzero-short-label route, including once-only T_ext=soft N^(31/192). No coprimality of hidden orders with k or N is added.

Each row hits at most one clock point at either prime, and no two rows hit the same clock point. Write s_p for that component's hit count. Then s_p<=min(J,h), and h<=ord_p(q)<p from clock separation; hence s_p<p. No unsupported inference J<p from soft-O notation is needed.

The target is the normalized reciprocal monic gcd H(Y), componentwise product_(hit rows)(1-Y y_j), OR a proper factor. This may have different degrees at the two components, in which case a factor-return branch is allowed. It is not presumed to be an already acquired polynomial over R=Z/NZ.

## 2. First-slice indicators from ONE-variable regularization

Treat the acquired y_j as INDEPENDENT formal row inputs, keeping q fixed; do not differentiate their beta-power construction. Define

    P(delta;y)=product_(j,i) [1-(1-delta)y_j/x_i]
              =sum_n a_n(y) delta^n.

Locally, its first order is s_p, and a_(s_p)=A_p, the nonzero product of nonhit constant factors. Find the first coefficient a_d not zero modulo N by precision doubling. A proper gcd of a_d factors; if gcd(a_d,N)=1, both local hit counts equal d and A=a_d is a global unit. The case d=0 returns H=1. In the covered complete query this case cannot persist, but it is valid for restrictions.

For d>0, define

    e_j = -y_j A^-1 [delta^(d-1)] (partial P/partial y_j)
        = -y_j A^-1 (partial a_(d-1)/partial y_j).    (1)

At a local hit row j, differentiating its unique hit factor gives constant -1/y_j, while the remaining hit factors supply delta^(d-1), so the extracted coefficient is -A_p/y_j. At a nonhit row j every differentiated summand still contains all d hit factors, so the coefficient is zero. Therefore e_j is EXACTLY the hit indicator 0 or 1 at each hidden prime.

Notably a_(d-1) vanishes at the actual input, but its gradient need not vanish. Replacing it by the constant zero function before differentiation would be wrong.

If some e_j is a mixed CRT idempotent, gcd(e_j,N) is proper. Otherwise every e_j is literally 0 or 1 modulo N, with the SAME hit membership at both components. Construct

    H(Y)=product_(e_j=1)(1-Y y_j)

by a product tree in soft J. It is the required reciprocal gcd at both components. This uses no factorial/Hasse normalization and no division by a collision value. It avoids acquiring the triangular bivariate delta,Y jet merely to discover the hit rows.

## 3. Fully initialized scalar circuit and its safe reverse pass

Here is an explicit version of the old scalar monic-block backend, so no black-box algorithm valid only on native inputs is differentiated. Put b=min(h,ceil sqrt(Jh)) and h=ab+r, 0<=r<b. Acquire

    B_b(T)=product_(t=0)^(b-1)(1-q^(-L-t)T).

Evaluate it at all J*a supplied points

    T_(j,v)=(1-delta)y_j q^(-vb), 0<=v<a,

by a subproduct/remainder tree with MONIC point divisors. Evaluate the analogous B_r at T_(j,a) for the tail. The product of all these values is exactly P(delta;y). Initialization is the empty product 1, and every clock position occurs exactly once. Acquisition/evaluation/product assembly cost

    C(J,h)=soft O(J+b+Jh/b)=soft O(J+sqrt(Jh))

ring operations. Repeated evaluation points and collision zeros are allowed. The block roots and points use only acquired q powers; no 1-q^n is inverted.

Run this circuit over A_d=R[delta]/(delta^(d+1)). Its coefficient rank is d+1, with soft O(d+1) multiplication cost. Monic remainder trees require inverses only of reversed monic polynomials with constant coefficient 1; their Newton series inversions remain units. The acquisition uses division-free polynomial products, acquired q^-1, and constant certified units of the inherited fast arithmetic; none are hit values. Fast polynomial multiplication may be implemented by arithmetic convolution kernels over this ring with certified constant-unit divisions, rather than differentiating a bit-level integer multiplication implementation.

Reverse arithmetic differentiation then computes ALL partial derivatives with constant-factor overhead measured in A_d operations. This statement needs no field theorem transplanted blindly: addition backpropagates its adjoint; multiplication z=uv adds adjoint(z)*v and adjoint(z)*u; a certified inverse z=u^-1 adds -adjoint(z)*u^-2. These identities hold over every commutative ring where that inverse exists. Start the scalar output adjoint at 1, retain the forward values, and traverse the actual arithmetic circuit backwards. The modulus delta^(d+1) is independent of y, so coefficientwise differentiation commutes with truncation. Polynomial subroutines can be expanded into these arithmetic gates. No numerical branching on a collision is differentiated.

Thus first-order search plus one reverse pass, indicator extraction, and H assembly cost

    soft O((d+1)(J+sqrt(Jh))+T_ext).              (2)

T_ext is paid only if a terminating legal factor/exponent branch uses it. Inverting A is certified by its explicit gcd=1. Formula (2) improves the previous triangular-jet factor (d+1)^2 to d+1, but even d=1 still pays the OLD scalar acquisition scale. It is an improvement in full-output precision overhead, not a faster factorer.

For attribution, reverse arithmetic differentiation is the Baur–Strassen method: [original 1983 paper DOI](https://doi.org/10.1016/0304-3975(83)90110-X). Publisher full text was inaccessible in this bounded search; the gate proof above supplies the exact ring version used here. The prior journal already credits Baur–Strassen; no novelty is claimed for that method.

## 4. Deterministic row restrictions remove jets, but not the scalar wall

There is a better output-sensitive alternative to (2). Evaluate the OLD scalar clock product on a row subset S. If its gcd with N is 1, discard S. If proper, return the factor. If N, bisect S and test the children. Start at all rows and stop at individual rows. All source labels and clock windows remain unchanged.

If no proper factor occurs, every retained leaf row hits BOTH components; discarded rows hit neither. Hence multiplying (1-Y y_j) for retained rows acquires the reciprocal gcd with no Hasse precision or gradient. If component hit memberships differ, some restriction eventually produces a proper gcd; different clock indices on the same surviving row do not invalidate this gcd output.

Let s be the number of rows hit at at least one component. At depth ell, at most O(min(2^ell,s)) nodes are tested, each of size O(J/2^ell). Summing the old subset cost gives

    soft O(J+sqrt(max(1,s) J h)+T_ext),          (3)

including the mandatory root test, logarithmic depth, source partitioning and final product assembly. The max(1,s) retains that root cost when a restriction has no hits. For early termination s may be the union count of the original instance. With no factor and equal hit counts d, s=d. Dense output costs soft J sqrt h; s=1 still costs the old soft sqrt(Jh). The algorithm does not need s in advance.

This is standard output-sensitive restriction/localization, concretely initialized for the native gcd output. For FACTORING, following just one nonunit path and then its original one-row clock consumer already suffices at soft(J+sqrt(Jh)+T_ext); listing all hits is unnecessary. Therefore neither (2) nor (3) is credited as complete-query exponent progress. Their possible use is to evaluate a proposed collision-retaining closure, not to replace the known factorer.

## 5. Primary q-holonomic/desingularization audit

[Bostan–Yurkevich, 2012.08656, section 3.4, Theorem 5](https://arxiv.org/html/2012.08656#S3.SS4) explicitly charges recurrence order and polynomial coefficient degree: the optimized block size balances degree times block length against the number of blocks. Its rank-one degree-J specialization retains soft sqrt(Jh), not soft sqrt h. Sections 2.1 and 3 provide the old geometric-factorial block method used above. Their several-index result shares values after that acquisition; it does not initialize the singular slice from free endpoints. This is known baseline credit, not a new literature gain.

[Chen–Kauers–Singer, Desingularization of Ore Operators, Theorem 6 and introduction](https://arxiv.org/html/1408.5512) removes removable LEADING factors by taking suitable least common left multiples. Its stated setup uses a characteristic-zero field and an order-increase parameter supplied as input. It is not itself a finite-composite-ring evaluation theorem. In our direct recurrence

    P_(i+1)=F_delta(q^-i) P_i, P_0=1,

with F_delta(X)=product_j(1-(1-delta)q^-L y_j X), the forward Ore operator S-F_delta already has leading coefficient 1. There is no leading factor for this desingularization theorem to remove. Backwards stepping divides by the very F_delta values that may collide; at such a step the forward map loses the predecessor amplitude. A different higher-order operator could conceivably trade degree for order, but would need a new paid operator construction, complete initialization, certified composite-ring pivots and an evaluation bound better than C(J,h). Neither cited theorem supplies those data.

No source provides the requested soft-k original whole-query algorithm in this pass. The concrete completed refinement is the composite-ring first-slice indicator identity and its linear-precision execution, with the stronger output-sensitive restriction alternative stated separately. The unresolved scalar acquisition remains the old original-query bottleneck, not an alleged impossibility theorem.
