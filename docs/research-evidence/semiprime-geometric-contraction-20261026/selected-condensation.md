# Selected tangent norm: an executed two-axis summation-by-parts reduction

26 October 2026. Scratch paper computation, no implementation or repository edits. Read separated-selector/separated-recurrence.md, recurrence-checkpoint/evidence/semiprime-tensor-norm-20261024/{scalar-resultant-algorithms,sylvester-elimination}.md, and direct-contraction/ternary-fusion.md. This does not repackage their initial Schur pivots or count a coefficient-algebra operation as a scalar operation.

**Outcome.** Two-axis barycentric reweighting supplies all short moments and an exact b+c-boundary/compact-interior reduction. Boundary acquisition and its factor gates are paid inside soft(J+b+c). The interior correction still contains the desired nonzero selected pole. Its numerators have acquired degree O(J), but their denominator remains four shifted copies of the row polynomial. No soft(J^(3/2)+b+c) selected norm evaluator is established. The precise next operation is this correlated mixed rational functional, not an uninitialized moment recurrence.

## 1. Actual acquired weights and short moments

After the literal-tail gate of separated-recurrence.md, use a full rectangle with b*c original clock leaves and exactly one good hit. Write x_u=q^u, y_v=Q^v, Q=q^b, and

    B(X)=prod_(u<b)(X-x_u), G(Y)=prod_(v<c)(Y-y_v).

Both are acquired monic polynomials. All differences within their grids have original q-exponents less than h and are certified units. Set

    alpha_u=x_u^(b-1)/B'(x_u),
    beta_v=y_v^(c-1)/G'(y_v).

These are GLOBAL units and acquired by derivative MPE and batch unit inversion in soft(b+c). The b=1 or c=1 formulas are interpreted with the empty product1. The weighted functional is

    Lambda[f]=sum_(u,v) alpha_u beta_v f(x_u y_v).

For each short k≥0 its moment is exactly

    mu_k=[b+k-1 choose k]_q * [c+k-1 choose k]_Q.     (1)

This follows from the finite Lagrange identity sum x_u^(b-1+k)/B'(x_u)=h_k(x_0,...,x_(b-1)), followed by geometric specialization. Thus mu_0=1, with initialized recurrence

    (1-q^(k+1))(1-Q^(k+1)) mu_(k+1)
      =(1-q^(b+k))(1-Q^(c+k)) mu_k.                 (2)

First O(J) moments cost soft J, NOT bc entries. Each division is by an actual screened q-gap. Uniformly for native K≥54, h≤(sqrt(2)/4)H+9 implies b=ceil(sqrt h)≤K, while J≤K/3. For k≤4J, the full original-q footprint is bounded by

    b(c+k+1)≤h+4bJ+b<2H,
    b+k+1≤7K/3+1<2H.

The first strict bound uses sqrt(2)/4+4/3<1.687 and its remaining K+9 margin at K≥54. Thus even TWICE the full moment footprint is <4H<16H. Every displayed numerator/denominator gap is covered by the actual inherited screen; no sufficiently-large qualification or inferred formal-ratio unit is needed.

These are not ordinary uniform trace moments and their low initialization is real. They do not alone initialize Lambda on arbitrary rational functions.

## 2. What this weighting preserves

Let H_w(t)=sum_j w_j prod_(k!=j)(t-T_k), acquired with F' by a product tree in soft J. Use the globally simple regularizer F(t)+delta and the paired sources

    f0_delta(t)=F'(t)/(F(t)+delta),
    f1_delta(t)=H_w(t)/(F(t)+delta).

At the unique good hit, residues under Lambda are alpha_(u*) beta_(v*) F'(T_hit) and w_hit times that same NONZERO good-field amplitude. Uniqueness implies F'(T_hit) is nonzero at the good field; no global row separation is required for this claim. The existing norm/coordinate gates either factor or license normalization; norm=N declines a wrong bin. Thus the pair suffices for the weak row-index consumer, although it is not numerically the original product derivative pair.

For comparison the simpler source 1/(F(t)+delta) has residue alpha_(u*) beta_(v*) itself, a global unit. Pairing THAT source with H_w/(F+delta) would incorrectly retain an extra F'(T_hit); it is not the marked ratio. The two explicit numerators above avoid this mismatch and preserve simple delta poles in every component, including repeated nonhitting rows. Everything below applies separately to these two rational sources, as well as to the simpler comparison source.

## 3. Finite double summation by parts, with ALL boundaries

Let A_u=sum_(r=0)^u alpha_r, C_v=sum_(s=0)^v beta_s. Their terminal values are1 by (1); acquire every prefix in soft(b+c). For ANY rational f defined symbolically at these nodes, exact telescoping gives

 Lambda[f]=f(x_(b-1)y_(c-1))
   -sum_(u<b-1) A_u [f(q x_u y_(c-1))-f(x_u y_(c-1))]
   -sum_(v<c-1) C_v [f(Q x_(b-1)y_v)-f(x_(b-1)y_v)]
   +sum_(u<b-1,v<c-1) A_u C_v
      [f(qQ x_u y_v)-f(q x_u y_v)-f(Q x_u y_v)+f(x_u y_v)].   (3)

Thus the boundary uses precisely the last row and last column, b+c-1 distinct original leaves. Acquire F and the marked leave-one-out numerator values there by monic MPE in soft(J+b+c). Norm/coordinate-gate the actual F values. Any nonunit localizes to one clock node and one of J actual row factors and factors via the original mixed-label decoder. Algebra/localization costs soft(J+b+c), with once-only original extraction soft K separately. On continuation every boundary denominator is a GLOBAL unit, so its delta residue is zero; no boundary physical hit is discarded.

This is a factor-or-interior reduction, not an assumption that unknown hits are away from endpoints. Cases b=1 or c=1 have only the boundary and are completed directly.

## 4. Execute the remaining rational mixed difference

For f_delta put, at variable t,

    a=F(t)+delta, b0=F(qt)+delta,
    c0=F(Qt)+delta, d=F(qQt)+delta.

The exact mixed difference in (3) is

    1/d-1/b0-1/c0+1/a
      = [b0*c0*(a+d)-a*d*(b0+c0)]/(a*b0*c0*d).      (4)

Its numerator has t-degree at most3J and delta-degree at most2. All four shifted coefficient arrays and numerator coefficients are acquired in soft J; for numerator p (F' or H_w), the corresponding explicit numerator is

    p(qQt)*a*b0*c0-p(qt)*a*c0*d
       -p(Qt)*a*b0*d+p(t)*b0*c0*d.

Its t-degree is at most4J-1 and delta-degree at most3, still soft-J acquisition with fixed delta rank. None of the four native denominators is inverted at its potentially colliding value: (4) is a cleared rational identity, usable through formal regularization or a separately guarded solver.

After the paid boundary gates, (3) therefore leaves a smaller rectangle of a rational function with acquired degree4J denominator and degree-O(J) numerator, multiplied by acquired prefix weights. This is compact actual input, but evaluating its selected Laurent coefficient still asks for a two-GP rational functional. Treating the denominator factors as four independent one-dimensional products would change (4).

There is an exact check that the correction has NOT lost the useful zero. In the simple-pole source, a unique interior node (u*,v*) appears in its four neighboring mixed differences. Its total coefficient on the right of (3) is

    (A_(u*)-A_(u*-1))*(C_(v*)-C_(v*-1))
       =alpha_(u*) beta_(v*),                      (5)

with the obvious boundary convention. This is the required nonzero good amplitude. For the actual pair of §2, multiply (5) by the common nonzero good factor F'(T_hit); its marked version is w_hit times that amplitude. Hence the interior correction cannot simply be dropped after its boundary values are found unit. Formula(5) is an actual finite pole-amplitude calculation, not a generic degree objection.

The polynomial numerator in (4) has short diagonal support in (S,Z), but its four reciprocal factors remain coupled in SZ. A degree-O(J) numerator is not itself a rank-O(J) matrix representation of the rational values. No claim about the rank or impossibility of another implicit solver follows.

## 5. Pearson version and what its boundary means

Equation(2), applied monomial by monomial, yields the initialized identity

 Lambda[(1-t)f(t)]
  =Lambda[(q^b-q t)f(qt)+(Q^c-Q t)f(Qt)
              +(qQ t-q^b Q^c)f(qQt)].              (6)

For rational f the same identity follows from the finite grid-weight recurrence, with the endpoint coefficients vanishing; it is not a free extension from truncated moments. It can be proved by summing either axis Pearson identity first, so the finite boundaries are already accounted for. Substituting 1/(F+delta) gives four correlated shifted denominators. Clearing them produces an acquired polynomial identity, but does not evaluate any one of the rational functionals. At a physical pole their residues obey the same known weight relation rather than an equation selecting the unknown index.

Thus (6) is an actual finite recurrence with seeds for its polynomial moments. Its rational-functional unknowns, or an equivalent selected singular solve, remain unpaid. Replacing this step by 'solve the moment recurrence' would reintroduce the missing operation in disguise.

## 6. Cost and next exact interface

Acquired: F and marks, both GP polynomials, unit barycentric weights, first O(J) mixed moments, b+c-1 actual boundary values and their factor gates, and both full degree≤4J-1 mixed-difference numerators. Total algebra soft(J+b+c), plus any once-only terminating soft-K extraction. At J≤K^(2/3), b,c=O(K), all of this fits the desired budget.

Unacquired: the marked/unmarked selected pole of the residual in (3)–(4), without materializing bc values or the old degree-Jb resultant. An algorithm contracting this specific prefix-weighted, four-shift rational correction in soft(J^(3/2)+b+c) would complete the row-index handoff. A method that only acquires its moments, formal Schur descriptors, or boundary-unit values does not do that.

All identities above are derived finite identities. Prior tensor-norm work already supplies initial fraction-free Sylvester steps, all formal q-hook pivot boundaries and their safe reversal divisions, but leaves mixed endpoint norms unpaid. This note tests a different actual cancellation and makes its finite correction explicit; it does not claim a new exponent or a generic obstruction to selected condensation.

## 7. Executed alternative: full-clock barycentric weights and a Pearson–Gosper numerator

This continuation replaces the separable two-axis weights by the FULL-clock weights, retaining an implicitly acquired functional. Put W(X)=prod_(i<h)(X-q^i) and

    omega_i=(q^i)^(h-1)/W'(q^i).

Every omega_i is a unit from actual short node gaps; an h-entry array is NOT claimed acquired. Instead its polynomial functional L is initialized by

    L[X^k]=[h+k-1 choose k]_q, L[1]=1,
    (1-q^(k+1)) mu_(k+1)=(1-q^(h+k)) mu_k.

The first O(J) moments and all coefficients below are acquired in soft J, with actual footprint h+O(J)<16H checked. This is the existing finite q-Pearson functional, not new first-discovery credit. Its exact finite identity is

    L[(1-X)g(X)]=L[(q^h-qX)g(qX)].                 (7)

At endpoints the missing terms have zero coefficient, so no nonunit denominator has been silently discarded.

Here is a concrete coefficient-level summation attempt for the ACTUAL paired sources. Set D=F+delta, p=F' or H_w, and allow an acquired polynomial weight A(X) of degree O(J). Seek a numerator P and polynomial remainder r such that

    A(X)p(X)/D(X)
      =(1-X)P(X)/D(X)
        -(q^h-qX)P(qX)/D(qX)+r(X).                (8)

If solved, the rational part telescopes by(7), and the polynomial remainder would be acquired from short moments. This is an actual initialized ansatz, not an unnamed q-Gosper call.

First gate F(1) and the ACTUAL one-step-extended value F(q^h); nonunits localize and factor, rather than receiving a unit assumption. The latter endpoint is essential: the zero of q^h-qX is X=q^(h-1), at which D(qX)=D(q^h), NOT D(q^(h-1)).

The extension has a licensed native label. In the rooted retuned parity bank write H'=K'^2, Q0=pi^H', the common clock q=Q0², a root T'=pi^[ell'+H'(M0-phase)]*barpi^(A+CN), phase in{0,1}, and padded length h=M0+1. The new endpoint corresponds to physical index i=phase+2h-M0=M0+2+phase≤M0+3. Its individual relation label is

    (ell'+H'(M0-phase-2h), A+CN).

The second exponent is nonzero by the retuned ellipse coefficient bound (nonaxis |A|≤2K'/sqrt(3)<N, with axes ±2K'). Both labels have O(log N) bits and use the SAME prepared pi,barpi. Thus the complete original-K mixed-label decoder applies after localization in ALL bins, with once-only soft-K charge; no arbitrary auxiliary polynomial zero is decoded. In a correct bin the true physical index bound |i|<M0 excludes this endpoint after the inherited alias argument: extending the former exponent magnitude bound by at most3H' still leaves it far below256H² under the original-K preparation and m³≤K/1024. Explicitly, with Dceil=ceil(sqrt(2K'N)), the extended magnitude is <8Dceil+(13/2)H'≤12K^(7/2)+7H+8<16H²<256H² for K≥54 and N≤K^6. This uses original K, not an unjustified N≤(K')^6 hypothesis. Hence the endpoint cannot silently remove the covered good attempt. An unpadded two-length bank must use each row's actual next index rather than this padded formula. Next run the previously paid native shifted-root gate for F(X),F(qX). A nonunit shifted resultant localizes to an actual mixed relation and factors; otherwise these polynomials are formally comaximal after regularization. These gates cost soft J algebra and at most the once-only original soft-K extractor. No arbitrary intermediate polynomial zero is assigned that decoder.

The FIRST necessary numerator in(8) is already computed explicitly. Let

    U(X)=(F(X)-F(1))/(X-1).

This is exact monic linear division, acquired in soft J. Since (1-X)U(X)=D(1) modulo D(X), define

    P0(X)=A(X)p(X)*U(X)/D(1) mod D(X).             (9)

The inverse uses the certified unit constant F(1), so fixed-precision jet calculation is lawful. This acquires the forced degree<J residue of P in soft J. There is no missing initialization or linear-system oracle at this step.

Clearing(8) gives

    Ap D(qX)=(1-X)P D(qX)
              -(q^h-qX)P(qX)D(X)+r D(X)D(qX).    (10)

Reduce modulo D(qX). Its other factors D(X) and q^h-qX are units: the first by the actual shifted-resultant gate, the second by the acquired F(q^h) one-step endpoint gate. Hence P(qX)=0 modulo D(qX), equivalently P=0 modulo D. Reducing(10) modulo D then forces Ap=0 modulo D.

At the actual unique good hit theta, F'(theta) is nonzero. Thus for the unmarked source p=F' and any A(theta) nonzero, that divisibility is impossible. For the marked source the same holds when its integer mark is nonzero in the good field, as true for row marks1,...,J. Therefore this candidate cannot eliminate the rational correction while preserving the useful pole. Choosing a polynomial A that makes it divisible merely annihilates the selected amplitude. The argument applies to the actual native good hit, not to a generic unrelated polynomial or a sample family. It is a scoped extension of the previously credited same-denominator certificate obstruction, now with an initialized full-clock functional and physical paired numerators.

An ansatz with additional shifted denominators can transfer the pole instead of killing it. Unless its acquired boundary then contains that transferred pole, a pole-free endpoint evaluation still cannot supply the desired residue. No lower bound on such a different transfer algorithm is asserted. Likewise a weight involving a singular inverse at a selected row could change(10), but acquiring and normalizing that singular inverse is precisely an additional operation; it is not a supplied unit weight.

The paid output of this attempt is (9), the exact finite certificate test(10), and a precise remaining equation: evaluate the residue of L[(1-X)P0/D] (and its marked counterpart), which equals that of L[Ap/D] because their difference is polynomial in X and regular in delta, or use a different initialized pole-transport denominator. This is again a Cauchy-type rational functional, not an acquired short-moment contraction. Neither replacing the axis weights by omega nor applying the concrete Pearson numerator ansatz supplies a faster scalar selector here.
