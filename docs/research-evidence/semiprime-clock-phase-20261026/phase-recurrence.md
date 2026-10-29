# Direct acquisition of one clock-phase bit: alternating pole and paired transfer

26 October 2026. Scratch paper execution, no frozen-file edits or long coefficient emission. **A fully initialized factor-or-phase-bit algorithm is obtained with query acquisition at the RETAINED soft(J+sqrt(Jh)) cost, plus a once-only soft-K terminating decoder if needed.** Its two-step transfer has a cancellation in its off-diagonal entry, but not the degree reduction needed for soft K. A specific same-denominator twisted antidifference attempt fails after a paid native shift gate. This is not a general obstruction to a direct phase supplier.

## 1. A smaller ONE-scalar bit target

Use the selected beta-coupled whole-bin singleton bank, monic D(X)=prod_j(X-T_j), q, and 0<=i<h. Its unique good collision is D(q^I)=0. Introduce the SHORT-POLYNOMIAL regularizer D(X)+delta and define

    Z_h(delta)=sum_(i=0)^(h-1) (-1)^i/(D(q^i)+delta),
    z_h=Res_delta Z_h.

At the good nonsplit prime this coefficient is EXACTLY (-1)^I, not an unknown unit multiple. Each summand is simple in delta in every component, regardless of repeated row roots or multiple distinct hits elsewhere. This is a changed sufficient readout, not equality with the earlier packed scalar or its physical leaf regularization.

An ACTUALLY acquired z_h supplies a bit with polylogarithmic validation. Its tau coordinate has gcd divisible by the nonsplit factor. A proper gcd factors; gcd one rejects a wrong bin; gcd N certifies a globally scalar value c. Test gcd(c-1,N), then gcd(c+1,N). Proper gcds factor, gcd N certifies respectively even or odd I. On a correct attempt at least one test cannot be one. Since N is odd the two signs cannot both hold globally. An unverified wrong-bin candidate is bounded failure and cannot stop later bins. This needs no small-integer scan, HH call or clock cofactor.

After truthful bits r=I modulo b have been acquired, rebase

    q'=q^b, D_r(X)=q^(-rJ)*D(q^r X),
    0<=i<ell_r=1+floor((h-1-r)/b).

D_r is an acquired monic degree-J polynomial. Its unique good root on that clock has index (I-r)/b; apply the SAME parity target to acquire the next bit. All leaves represent original indices r+b*i; no artificial phase relabelling or length stretching is used. Stops at b>=max(1,h/K) yield the previously proved soft-K shortened final query. Only O(log K) bits are required. What remains is acquiring each z_h cheaply, not validating the bits.

## 2. Execute a fixed-rank fraction-free bit algorithm

Put f_i=D(q^i)+delta and define polynomials P_i=prod_(k<i) f_k, N_i=P_i*sum_(k<i)(-1)^k/f_k. Before specialization,

    [N_(i+1),P_(i+1)]^t
    =[[f_i,(-1)^i],[0,f_i]]*[N_i,P_i]^t,
    [N_0,P_0]^t=[0,1]^t.                              (1)

There is no division by a native value. At a correct singleton,

    P_h(0)=0, P_h'(0)=prod_(l!=I)D(q^l)!=0,
    N_h(0)=(-1)^I*P_h'(0).                            (2)

Thus only the two constant-depth outputs N_h(0),P_h'(0) suffice to supply the bit. Their ratio is a weak readout: it need not equal the actual z_h in wrong bins or other components with different zero multiplicities. Norm-test P_h'(0), factor or invert only a certified unit; its good value prevents the saturated failure branch. The ratio then passes the same +/-1 bit validator of §1. This is legal global-unique first-variation machinery, not a new claim that an empty-block ratio is meaningful.

Pair the even/odd steps. With X=q^(2t), f_e=D(X)+delta and f_o=D(qX)+delta, the EXACT paired matrix is

    M(X)=[[A(X),B(X)],[0,A(X)]],
    A=(D(X)+delta)*(D(qX)+delta),
    B=D(qX)-D(X).                                    (3)

The delta terms cancel COMPLETELY in B. Every pair matrix is A*I+B*E12, so all such matrices commute; E12²=0. At a unique pair hit the residue of B/A is +1 for its even leaf, -1 for its odd leaf. No unknown derivative amplitude remains after the ratio (2).

An odd final clock leaf is handled explicitly: evaluate its D(q^(h-1)) in soft J. A nonunit value localizes to an ORIGINAL row leaf and factors by its actual mixed-label consumer. Otherwise it is a certified unit, so its term has zero residue and may be omitted for this bit. This is a paid actual endpoint gate, not deletion of an additive source zero.

### All initialized coefficients and cost

A has degree 2J, B degree at most J; their coefficients in the constant-rank delta jet are acquired in soft J. No h-entry array of D(q^i) is supplied. For a block of t paired steps, acquire the polynomial matrix

    M_t(X)=prod_(s=0)^(t-1)M(q^(2s)X).

Its degree is at most 2J*t, with fixed matrix/jet rank. Shifted coefficients, product-tree multiplication and all coefficients cost soft(J*t). Evaluate at the actual giant starts q^(2t*k), with monic MPE, costing soft(J*t+h/t). Multiply the resulting constant matrices and process the final truncated block, charged at the same bound. All operations are division-free polynomial/ring operations before the ONE final ratio gate. Taking t=max(1,ceil(sqrt(h/J))) gives

    soft(J+sqrt(Jh)).                                 (4)

At the native h~K^(3/2),J~K this is K^(5/4), not K. The algorithm may already factor by localizing the emitted P_h(0); that is the inherited norm-query option, not a new rate. Even if it returns a phase bit instead, successive truthful rebased horizons halve, so the square-root costs sum geometrically and the J setups add only logarithms. Thus this is an ACTUAL initialized phase acquisition route at the retained soft(K+sqrt(Jh)) complete bound, with no full h coefficient list or unresolved initial value.

## 3. Try to exploit the off-diagonal cancellation further

There is a paid polynomial q-antidifference of B under the PAIRED clock. Define

    H(X)=sum_(r=0)^J d_r*X^r/(1+q^r).

All denominators are certified units: r=0 uses 2, and for r>=1 use (1-q^(2r))/(1-q^r). On a rebased bit stage the same check uses original exponents at most 2*b*J. Before the stopping modulus, and for its last doubled stage if needed, b<2h_original/K and J<=K/3, so 2*b*J<4h_original/3<3h_original<16H using the explicit inherited h_original<=8K^(3/2)+9 and K>=54, not merely h_original<16H. Thus these are ACTUAL inherited unit certificates, not a new global-order assumption about q-prime. Hence H is acquired in soft J and

    H(q²X)-H(X)=D(qX)-D(X)=B(X).                       (5)

This looks promising but is NOT yet an antidifference of B/A. Write p_t=H(q^(2t)), m_t=H(q^(2t+1)). Then

    D(q^(2t))=p_t+m_t,
    D(q^(2t+1))=m_t+p_(t+1),
    B/A=(p_(t+1)-p_t)/[(delta+p_t+m_t)*(delta+p_(t+1)+m_t)]. (6)

The offset m_t moves between adjacent pairs. The reciprocal difference telescopes within a pair but not across the next pair. Dropping that moving offset would change the actual finite source. Equations (5)–(6) are an executed cancellation with all new coefficients acquired; they do not remove A or shorten its degree 2J. A recurrence for this correlated staggered source could still be useful; no such initialized nearlinear contraction is established here.

A sharply scoped rational-certificate test also fails. Seek the signed source's antidifference in the SAME row denominator, R=P/(D+delta), deg P<J, satisfying R(X)+R(qX)=1/(D(X)+delta). Clearing gives

    P(X)*(D(qX)+delta)+P(qX)*(D(X)+delta)=D(qX)+delta.    (7)

Actually run the short native shift-separation gate: acquire D(q*T_j) by MPE. A nonunit localizes to an actual T_j-q*T_k relation; its mixed label is nonzero because equal coefficient pairs would require a centered phase difference H. The actual mixed decoder factors. On continuation D(X) and D(qX) have unit resultant, so D+delta and D(qX)+delta are formally comaximal. Reducing (7) modulo each denominator forces respectively P=1 and P=0 modulo D+delta, impossible at degree<J. This rules out THAT same-denominator certificate, not certificates with shifted poles, another deformation, or a direct selected-residue algorithm. No arbitrary additive pivot is assigned the mixed decoder.

## 4. Roots-of-unity evaluation: account for the truncated Euler tail

At the GOOD field, the pole-kernel gauge gives c(z)=lambda*z^I*B(z) modulo z^h. The following single-mode evaluation is not asserted globally when other components have multiple hits. It is tempting to evaluate c at +/-1 and divide by B to recover (-1)^I. That factorization is only a TRUNCATED product. For B_L(z)=sum_(m<L)q^(m(m-1)/2)z^m/(q;q)_m, direct finite telescoping gives

    B_L(-1)=(-1)^(L-1)*q^(L(L-1)/2)/(q;q)_(L-1).

With n=h-1 this yields the exact relation

    c(-1)=(-1)^n*q^(n-I)*c_n.                          (8)

The putative (-1)^I phase has been absorbed by the omitted tail; the result depends on the full theta=q^I. Properly computing B^-1*c modulo z^h before evaluating would recover the phase, but its full h-vector is NOT acquired in soft J. Equation (8) is a finite tail correction, not a general argument against other selected evaluations.

For a dyadic root of unity zeta, the deconjugated evaluation is genuinely a phase character, but acquiring it is the weighted finite sum itself; adjoining zeta or naming the projection does not pay that sum. The scalar +/-1 target of §1 avoids any extension and shows that even the first bit can be asked for with an exact bounded output. It remains an acquisition target, not known measured information.

## 5. Finite boundary and scope

The alternating finite sum obeys the exact anti-shift law

    Z_h(qX;delta)+Z_h(X;delta)
    =1/(D(X)+delta)-(-1)^h/(D(q^h X)+delta),           (9)

where Z_h(X;delta)=sum_(i<h)(-1)^i/(D(q^i X)+delta). This finite anti-shift law retains its endpoint source; it does not acquire the intervening indicators D(q^i)=0. No additional pole-free post-window claim is used. Formulas (1)–(4), rather than the boundary relation alone, give the completed numerical algorithm.

All identities above are finite and derived directly. Prior credit: the frozen unique-pole/unique-weighted first-variation gates, scalar-acceleration Newton/pole gauge, and original shared division-free geometric engine. This investigation does not reuse an ordinary Bostan–Mori constant-order bound for growing-degree coefficients. It isolates a one-scalar phase-bit target, executes a fraction-free paired transfer with a real off-diagonal cancellation, and charges its full coefficients/tails. The retained cost is K^(5/4); a soft-K acquisition of the alternating residue or its weak first-variation pair is still missing. No general phase-supplier lower bound is claimed.
