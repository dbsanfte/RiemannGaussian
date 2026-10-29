# Direct Lucas readout: unit Cassini invariant and the exact missing finite part

26 October 2026. Paper-only constructive attempt on the actual torus-only bank. No repository edits, code, numerical campaign or Lean. **A soft-K initialized endpoint computation is executed. Its exact cancellation formula retains the interior hit count as a finite-part correction, so it is not a fast zero-query algorithm.** This is a scoped evaluation of one Casoratian candidate, not the old fixed-degree q-Gosper objection or a general impossibility claim.

## 1. Native inputs and all legal guards

Use the complete factor-or-prepared torus-only branch of `torus-query.md`: unchanged scalar beta and D, the actually projected norm-one W with odd K-rough coprime local orders>16H, q0=W^H with its actual short-unit screen, and separately acquired weighted bins. Keep their nonzero integer labels and all signs/axes. The correct nonsplit-factor bin is guaranteed to hit; every actual nonzero short W-annihilator now factors in soft K through the licensed torus-to-beta transfer, without exact integer/tag provenance.

All native exponents are even. Define k=H/2, sigma=W^k, t=Tr(W), c=Tr(sigma), and

    L_m=(W^m−W^-m)/(W−W^-1).

The denominator is a certified unit: its squared value t²−4 is a scalar unit by the norm-one order screen. The quotient is a scalar and obeys L_-m=−L_m. For normalized clock i=0,...,h−1 put

    d_j=(ell_j−a_j−b_j N+H M0)/2,
    s_(j,i)=L_(d_j−k i), h=2M0+1.

The actual torus leaf is W^(2(d_j−ki))−1. Since all local W orders are odd, s_(j,i)=0 at a component iff that leaf vanishes. No root of unity or numerical order is introduced. Each row has at most one hit per component because h<16H and the q0 differences are actual units.

Acquire c, all first two row values and the common matrix T=[[c,-1],[1,0]] in soft K. Then

    s_(j,i+2)=c*s_(j,i+1)−s_(j,i).

The coefficients and seeds are fully acquired native scalars, not symbolic functions requiring a later spectrum computation.

For the endpoint experiment extend each row through i=h+1. If an integer literal zero label occurs at i=0 or i=h, omit that whole row: every original i differs by at most h and its other leaves are certified units. This cannot delete a witness. Actual nonliteral nonunit s_(j,0) or s_(j,h) immediately factors: a proper scalar gcd factors directly, while global zero gives a nonzero W-annihilator and the licensed terminating transfer. No zero scalar denominator is silently inverted.

Common matrix powering acquires s_h,s_(h+1) for ALL rows in soft(K+log h), not h steps per row. On no-factor continuation s_0 and s_h are global units and all endpoint ratios below are legally initialized.

## 2. A stronger shared invariant: the Cassini constant is row-independent

The explicit W-power formula gives, for every row and index,

    s_i*s_(i+2)−s_(i+1)²=−D,
    D=L_k².                                             (1)

Indeed the product of the two geometric amplitudes is −1/(W−W^-1)², independent of d_j. Thus D is COMMON to all rows, not just constant within one row. D is a global unit because sigma−sigma^-1 is a unit by q0−1 screening. Also c−2 is a unit: c−2=−Norm(sigma−1), and sigma−1 is a unit since (sigma−1)(sigma+1)=q0−1 is a unit.

This is a genuine cheaply acquired common conic constraint,

    s_i²+s_(i+1)²−c*s_i*s_(i+1)=D.

At an actual component hit s_I=0, odd order forces W^(d_j−kI)=1. Consequently s_(I−1)=+L_k and s_(I+1)=−L_k, with known unit values. This additional native information will determine the cancellation below. It is not assumed for arbitrary solutions of an order-two recurrence.

## 3. Execute endpoint Casoratian telescoping with its full regulator

Put a_i=s_i+delta. The target per-row count is

    V_j=[delta^-1] sum_(i=0)^(h-1) 1/a_i.

At every component V_j is exactly its 0/1 row-hit flag. A total count or a weighted count can be formed if these residues are actually acquired; the new annihilator decoder is not applied to an arbitrary additive zero of their formulas.

The regulated sequence is inhomogeneous:

    a_(i+2)=c*a_(i+1)−a_i+(2−c)*delta.

Do not assume that its Cassini invariant remains D. Direct subtraction gives

    a_(i+1)²−a_i*a_(i+2)
      =D+delta²*(c−2)−delta*(c−2)*a_(i+1).

Therefore the following exact rational identity holds after clearing denominators:

    [D+delta²*(c−2)] * T_j(delta)
      = a_1/a_0 − a_(h+1)/a_h
        +delta*(c−2)*S_j(delta),                     (2)

where

    T_j(delta)=sum_(i=0)^(h-1) 1/(a_i*a_(i+1)),
    S_j(delta)=sum_(i=0)^(h-1) 1/a_i.

Every summand has at most a simple pole at zero: adjacent s_i cannot both vanish because D is a unit. All endpoint ratios in (2) have globally unit constant denominator by §1. Thus they can be evaluated to any fixed precision in soft K total. The multiplier on T also has unit constant D. These are actual composite-ring operations, not field-only divisions.

Taking the delta^-1 coefficient in (2) proves that T_j has NO negative Laurent term. Equivalently at an interior hit its two adjacent terms have residues

    1/s_(I−1)=+1/L_k, 1/s_(I+1)=−1/L_k,

which cancel exactly at that actual native hit. If the last original position hits, the adjacent term using a_h supplies the same cancellation; a_h is already guarded unit. Endpoint-only telescoping consequently has no hit residue to read.

More precisely, write E_j(delta)=a_1/a_0−a_(h+1)/a_h. The constant coefficient of (2) is

    D*[delta^0]T_j = E_j(0)+(c−2)*V_j,
    V_j=(D*[delta^0]T_j−E_j(0))/(c−2).             (3)

D and c−2 are actual units, and E_j(0) is acquired in soft K. Thus the normalized hit flag is exactly an interior FINITE-PART correction to the cheap endpoint calculation. Assigning [delta^0]T_j=E_j(0)/D would erase every hit; it is not a lawful consequence of unregulated telescoping at singular inputs.

This identifies a smaller potential sufficient statistic: the simultaneous finite parts of these adjacent-resolvent sums, or just their sum with a proved noncancelling readout. It does not compute them. The correction is not an unknown multiplicative product amplitude; it is exactly the desired 0/1 residue.

## 4. Can a homogeneous regulator avoid the correction?

There is an initialized alternative deformation that preserves the order-two recurrence. Put b_i=C_(d_j−ki)(t)/2 and a_i=s_i+delta*b_i. All b_i seeds and endpoints are paid by the same W powers, since 2 is a unit. At a native hit b_I=1, so the residue of 1/a_I is still exactly one. The homogeneous Cassini identity has a row-independent deformed invariant, and its adjacent-resolvent sum telescopes exactly to endpoints.

This does not improve selection: the same interior pole cancellation is then exact for the entire rational family, not only its principal part. It computes a different regular observable and does not express the unpaired sum of reciprocals. Preserving the recurrence by deformation is therefore not a license to identify an endpoint invariant with V_j.

Likewise, evaluating the projective Riccati iterate s_(i+1)/s_i by binary powering T skips intermediate denominators. A nonunit endpoint is useful and handled, but unit endpoints do not certify unit interior s_i. Conversely explicitly visiting and guarding every Riccati pivot tests h steps per row, costing O(Jh) arithmetic. Neither implementation gives a new whole-query bound.

## 5. Paid completion and next narrow operation

The native s_i are BASE scalars. Acquire the row VALUES P_j=product_(i<h)s_i by the already initialized torus geometric engine and its explicit known unit normalization. A proper gcd(P_j,N) factors. On no-factor continuation gcd 1 gives flag V_j=0 and global zero gives V_j=1, since each component has at most one clock hit. These row values alone therefore acquire every actual flag. Equation (3) then computes each finite part from the already acquired E_j(0), D and c. No additive derivative, undeveloped Lucas jet deformation or higher Hasse slice is needed. The total remains soft(J+sqrt(Jh))=soft K^(5/4) over bins; no h-entry coefficient expansion or both-prime hit identification is assumed.

All cheap endpoint data in (2)–(3), the common invariant D, c−2 inverse, and the raw seeds are actually acquired in soft K. The first unpaid operation for this concrete approach is simultaneous [delta^0]T_j (or a safely aggregated version) on the native d_j list. A positive theorem directly acquiring those FINITE PARTS could avoid the old row-value computation; the displayed Cassini identity specifies exactly what it must preserve. Row values already supply them at the retained baseline, without jets. No field order, future-pivot guarantee, generic q-Gosper impossibility or broad lower bound is asserted.
