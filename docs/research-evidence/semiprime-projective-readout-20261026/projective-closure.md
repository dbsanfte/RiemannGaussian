# Joint projective readout: nonlinear reset and rational-certificate tests

26 October 2026. Scratch paper pass; no repository edits, tests, numerical campaign or Lean. **No cheaper coefficient/ratio acquisition obtained.** Two concrete JOINT tagged/untagged eliminations are executed. One now has a paid initial chart and unit increment, while future pivot certificates and fast advancement remain open; the other is forced to output the known global tag average, which cannot be the factor tag. Neither is a general obstruction to compressed readouts.

Inputs read: frozen coefficient-forms/README.md, its structured/residue/combinatorial expressions, the uniform hybrid-handoff.md sections 1–4, and the prior hybrid-audit/moment-locator.md. The old q-product, three-state/cofactor and finite endpoint constructions are prior credit. This report does not repeat the short-Prony or missing-diagonal displacement argument as a new result.

## 1. Exact acquired data and initialized coefficient recurrence

For either uniform monic family retain all unit tags j modulo K, row roots y_j, labels w_j=[j]_n with n|K and n>2, q=pi^H, J=phi(K)<=K, and clock h=2H+1. One family has exactly one row-clock hit at the good nonsplit field, whose tag is R mod n. The other prime has no uniqueness promise. Root powering, all label metadata and the following THREE polynomials are actually acquired in soft J:

    f(X)=product_j(1-y_j X),
    v(X)=sum_j product_(l!=j)(1-y_l X),
    u(X)=sum_j w_j product_(l!=j)(1-y_l X).

Use weighted product trees; no F'(y_j) inverse or global row separation is needed. Degrees are J,J-1,J-1. The exact marked clock block has first jet

    product_j[1-y_j X+delta(1-Yw_j)]
       =f(X)+delta[v(X)-Y u(X)] mod delta².

Thus with X_i=q^-i and f_i=f(X_i), etc., the actual initialized state is

    (P_0,V_0,U_0)=(1,0,0),
    P_(i+1)=f_i P_i,
    V_(i+1)=f_i V_i+v_i P_i,
    U_(i+1)=f_i U_i+u_i P_i.                    (1)

The terminal U,V are exactly the requested first coefficients. At the unique good-field hit I, P_I is nonzero, f_I=0, v_I is nonzero and u_I=w_* v_I. Consequently (1) resets P to zero and (V,U) to the nonzero scale v_I P_I times (1,w_*). Subsequent nonhit steps preserve that ratio. This is a lawful finite initialization through collisions.

The constant-size polynomial transition matrix in (1) has growing coefficient degree J. Acquiring its block coefficients and all giant evaluations, with the real start/tail, still costs

    soft O(J+sqrt(Jh))=soft O(K^(3/2)).          (2)

No free value of f_i, v_i or u_i across the long interval is assumed. The three-state form is old acquisition at that bound; it serves to test an actual nonlinear elimination rather than another abstract short recurrence.

## 2. Eliminate the amplitude: exact scalar nonlinear law and paid initialization

On a chart where V_i and V_(i+1) are units put t_i=P_i/V_i and r_i=U_i/V_i. Then

    t_(i+1)=f_i*t_i/(f_i+v_i*t_i),
    r_(i+1)=(f_i*r_i+u_i*t_i)/(f_i+v_i*t_i).    (3)

Solving for t gives, where the indicated divisions are legitimate,

    t_i=f_i*(r_(i+1)-r_i)/(u_i-v_i*r_(i+1)),
    t_(i+1)=f_i*(r_(i+1)-r_i)/(u_i-v_i*r_i).

Eliminating t between consecutive steps yields the CLEARED scalar relation

    f_i*(r_(i+1)-r_i)*(u_(i+1)-v_(i+1)*r_(i+2))
      =f_(i+1)*(r_(i+2)-r_(i+1))*(u_i-v_i*r_i). (4)

This is an explicit second-order nonlinear coefficient/clock law, with all its polynomial coefficient data acquired. Its INITIAL ratios and increment are now paid by [initial-chart.md](initial-chart.md): acquire the first 5J block values and raw states in soft J, classify nonunits by legal recovery, then select among c=0,1,2 a chart U/(V+cU) with two adjacent globally unit denominators and a certified global unit ratio increment. The chart uses the already acquired coefficients with v replaced by v+c*u. This resolves the initial-chart issue, but does not yet yield a fast complete selector:

* The raw ratio at time zero remains undefined, but the proved soft-J prefix supplies valid adjacent initial ratios and a unit increment in the selected three-chart coordinate. This is no longer an unpaid acquisition obstruction. Later chart denominators may still vanish by additive cancellation; the native q-order guard does not certify every future pivot.
* At index I, f_I=0 makes (4) constrain the subsequent constant tail rather than directly set its value. The PRECEDING equation at I-1 reads f_(I-1)*(r_I-r_(I-1))*(u_I-v_I*r_(I+1))=0. If its first two factors are certified units, it DOES enforce the correct reset. The initial chart/increment conditions are now certified by the short-prefix theorem; their persistence at later steps is not supplied. If a later increment vanishes, that constraint can be lost. ALL constant r sequences satisfy the cleared law. Thus one cannot claim that the cleared law universally erases the reset, or that it supplies a uniquely initialized selector. Inverting the eliminated expression at the hit would involve u_I-v_I*r_(I+1)=0 and is illegal.
* A vanishing additive chart pivot has no automatic original-leaf annihilator label. Proper integer gcds may factor, but a saturated pivot cannot simply be inverted or handed to T_ext. Retaining the homogeneous triple (1) avoids these invalid divisions and restores the exact reset, at cost (2).

Thus this projectivization now has acquired starting ratios and a nonzero increment, but still lacks a fast long-advancement algorithm and certificates for every future chart/pivot needed to select its singular-step branch. The initial-chart theorem also keeps the chosen coordinate valid locally at the actual hit and provides its exact tag conversion; it does not certify the whole intervening scalar stepping trace. This is not a lower bound on other nonlinear/projective recurrences or alternative finite charts with extra acquired data.

## 3. A genuinely joint rational-tail certificate

The frozen directional data are already acquired:

    F(X)=product_j(X-y_j),
    H0(X)=sum_j y_j F(X)/(X-y_j)=X F'(X)-J F(X),
    Hw(X)=sum_j w_j y_j F(X)/(X-y_j).

Test the stronger JOINT cancellation, rather than the old untagged test alone. Seek a rational A(X) and scalar r such that

    A(qX)-A(X)=Hw(X)/F(X)-r*H0(X)/F(X).         (5)

If this supplied a selector, tagged and untagged Cauchy tails could potentially be combined before acquiring their long common scale. The rational functions on the right are explicit soft-J data, including possible repeated roots: they equal sum_j (w_j-r)y_j/(X-y_j), with multiplicity.

### Actual native finite-orbit calculation

At the good nonsplit field, beta and W have coprime odd orders dividing R-1 and R+1. Consequently barpi belongs to the cyclic subgroup generated by pi: choose the proof-only exponent with residues +1 and -1 modulo those two orders. The supplied K-roughness makes H coprime to ord(pi), so q=pi^H generates that SAME subgroup. Therefore ALL supplied row roots pi^ell barpi^(a+bN) lie in ONE finite q-orbit, namely <q>. No discrete logarithms or orders are acquired by this proof.

For a rational function A over the good field, consider the differential A(X)dX/X. Pullback by X->qX permutes its residues on every finite nonzero q-orbit. Hence the sum of residues of [A(qX)-A(X)]dX/X over one orbit is zero. This is elementary finite-orbit algebra; no characteristic-zero or non-root-of-unity theorem is invoked.

Each summand y_j/(X-y_j) has residue 1 after multiplication by dX/X. Applying the necessary condition to (5) gives

    sum_j w_j-r*J=0, so r=(sum_j w_j)/J.        (6)

J<R, so this division is valid at the good field. The order of q need not be known, and higher poles of a putative certificate do not alter the residue-permutation identity.

### The forced answer is wrong on the ACTUAL complete unit-tag lists

Reduction of (Z/K)^times onto (Z/n)^times is surjective with equal fibers. For n>2 the sum of canonical unit residues modulo n is n*phi(n)/2. Thus for these full monic lists,

    (sum_j w_j)/J=n/2 in the good field.        (7)

It cannot be the actual factor residue r=R mod n. If n is odd, 2r=n has no integer solution 0<=r<n; the same conclusion holds modulo R since |2r-n|<2n<R. If n is even and n>2, n/2 is not a unit modulo n, whereas the factor residue is a unit. This disproves THIS joint rational-certificate selector on every good full unit-tag input, without a numerical example or arbitrary-root substitution.

Pruning/reweighting the row list changes the average and would require its own coverage/provenance proof; equation (7) is not claimed for arbitrary masks. Equation (5) does not exclude other rational readouts, finite differences with extra boundary data, or a matrix-valued certificate.

## 4. Why the known q,F do not yet give a finite-window residue

The correct tag is the residue ratio restricted to poles whose q-index lies in the physical window 0,...,h-1. There is exactly one such row root at the good field. Summing that RESTRICTED residue gives the desired label; summing the full orbit gives (7). The restriction is precisely the unacquired clock-membership mask. An arbitrary rational certificate without this finite-window boundary has no way to replace the global orbit sum by the restricted one.

A certificate can retain explicit interval endpoints or a rational tail; then its finite summation leaves those boundary values. Their formal definition is not their initialized evaluation, and evaluation at the collision must be cleared or regularized rather than inverted. Acquiring the full G(y_j) vector, original first-jet values, or the known row cofactor sums is still a sufficient route at (2). None has become a soft-J input of (5).

The necessary full-orbit condition can be proved with a very large unknown finite orbit. It is not claimed that every possible rational certificate must have that full degree: short acquired pole-shift chains could allow sparse certificates. No such uniformly useful chain/certificate or interval-sensitive scalar evaluation is supplied here.

## 5. Primary source scope and result

Rechecked [Chen–Singer, Residues and Telescopers for Rational Functions](https://arxiv.org/html/1203.4200), section 2 and section 4.1.3. Their setup explicitly assumes characteristic zero and q not a root of unity. The residue viewpoint motivates (5), but their summability criterion is NOT transplanted to the native finite fields. The finite-orbit necessary condition above is proved directly and does not use a sufficiency claim from that source. This avoids silently using the old non-root-of-unity obstruction at native q.

The concrete new tests here are the cleared JOINT nonlinear ratio law (4), now initialized by the proved soft-J prefix and three-chart theorem but without fast long advancement or future-pivot certificates, and the actual-family JOINT rational certificate (5), forced to the invalid tag average (7). All starts and safe homogeneous fallback costs are explicit. No soft-K readout algorithm, whole-query improvement, or general impossibility is established. The remaining constructive question is an initialized interval-sensitive cofactor/ratio operation that preserves the reset or restricted residue without paying (2); another global endpoint cancellation alone does not supply it.
