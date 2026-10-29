# Conditional global uniqueness: gate-free consumers and an executed short-moment attempt

26 October 2026. Paper-only finite calculation; no frozen-file edits, implementation or tests. Assume the proposed native covering construction has been proved to supply O(K) original beta-coupled rows, h=O(K^(3/2)), and EXACTLY ONE good-field hit in the entire correct bin. This report does not prove that cover. **Global uniqueness removes the empty-block gate from two useful weak-output consumers. The concrete normalized modified-moment algorithm below remains missing its finite-clock condition and does not improve acquisition.**

## 1. Actual finite Lambert contract

Integration note: the required cover is proved in [unique-cover.md](unique-cover.md)
and independently audited in [review-unique-cover.md](review-unique-cover.md).
On any attempted bin, a saturated denominator norm means bounded failure;
only an actually certified unit is inverted. The correct-bin theorem proves
that its required good-field denominators cannot take that failure branch.

Keep the actual original beta-coupled roots T_j, constant canonical tag u_j and rho=q^-1; do not transfer this promise to the raw torus-only aliases. At the nonsplit good field R, the correct bin has a unique pair (j*,I), 0<=I<h. Its tag is the actual factor square residue. Other components need not have a unique hit. The short q-order screen supplies all differences through 16H as genuine global units.

Let x_i=rho^i and c_i=(-1)^i rho^(i(i+1)/2)[h−1 choose i]_rho. The c_i are unit FORMULAS, not an emitted length-h array. Define Lambda(P)=sum_i c_i P(x_i). The two actual Laurent targets are

    V=Res_delta Lambda(sum_j 1/(1+delta−T_j X)),
    U=Res_delta Lambda(sum_j u_j/(1+delta−T_j X)).

At the good field (V,U)=(c_I,c_I*u_j*), with c_I a unit. Thus any correctly acquired common nonzero amplitude ratio suffices. No positive-count noncancellation lemma is needed in that field now. The existing norm/coordinate validator and bounded tag/HH recovery handle other components or wrong bins, with verified factors only. Continue after a failed wrong-bin attempt.

## 2. Two whole-bin consumers really no longer need an empty gate

First let P(delta,epsilon)=product_(j,i)(1+delta−T_j rho^i+epsilon*u_j). Ask ONLY for A=partial_delta P(0,0) and B=partial_epsilon P(0,0). In the correct good field, exactly one factor vanishes, so

    A=product_(nonhit leaves) leaf !=0, B=A*u_j*.

The value P(0,0) is not required to consume this pair: good-bin nonemptiness is already promised. Norm(A) yields a proper factor or certifies its global inverse (it cannot be saturated at the good field). B/A then gives the tag there. Wrong-bin unit ratios may be arbitrary and merely generate bounded factor-or-failure attempts. This is NOT an exact residue formula in a wrong bin, nor a claim that P(0,0)=0 globally without testing it.

The old constant-rank product engine acquires A,B in soft(J+sqrt(Jh)), and naturally may also emit P0. Removing its need as a consumer gate does not by itself make those coefficients cheaper.

Second put D_row(Z)=product_j(Z−T_j), W_row(Z)=product_i(Z−rho^-i). In the correct good field their gcd has degree one, even if D_row repeats at OTHER roots. Its canonical first subresultant is

    Sres_1(D_row,W_row)=a Z+b, a!=0,
    theta=−b/a=T_j*.

Thus only these TWO coefficients, not the resultant/empty gate, suffice. Given a,b, norm-test a; a proper factor terminates, otherwise a is a certified unit on the promised branch. Evaluate the acquired weighted cofactor H_u and D_row′ at theta. The unique row at theta gives D_row′(theta)!=0 and H_u(theta)/D_row′(theta)=u_j*. This second inverse is likewise unit-or-proper-factor by good-field nonvanishing. Evaluation costs soft J. Wrong-bin arbitrary subresultant candidates are checked by the same bounded tag consumer and cannot suppress later bins.

This differs from the older singleton-BLOCK target: a correct bin could contain empty blocks, so selecting its first arbitrary unit coefficient needed an empty-block gate. With guaranteed GLOBAL correct-bin nonemptiness, that gate is genuinely unnecessary. Acquiring a,b directly from the implicit clock is still open; once actual remainders are supplied, guarded fast half-GCD already acquires them at the old bound.

## 3. Execute short modified-moment initialization

A plausible direct scalar route is to divide the finite functional by its short row denominator and use only the rank-one pole moments. Let A_delta=1+delta and define

    D_delta(X)=product_j(A_delta−T_j X)=sum_(l=0)^J d_l(delta) X^l,
    N_0(delta,X)=sum_j product_(k!=j)(A_delta−T_k X),
    N_u(delta,X)=sum_j u_j product_(k!=j)(A_delta−T_k X).

All these short polynomials to fixed delta precision are acquired in soft J by product trees. d_J=(-1)^J product_j T_j is a certified constant unit. Repeated row roots cause no inversion.

The ordinary functional moments are explicitly

    mu_k=Lambda(X^k)=(rho^(k+1);rho)_(h−1),
    mu_(k+1)/mu_k=(1−rho^(h+k))/(1−rho^(k+1)).

Acquire mu_0 by the scalar q-factorial engine in soft sqrt(h), then O(J) moments using the displayed unit ratios; h+O(J)<16H is covered by the actual screen (or its explicit native guard). All rational inputs and these moments therefore cost soft K, without emitting h coefficients.

Let

    Y_k=Lambda(X^k*N_0/D_delta),
    Z_k=Lambda(X^k*N_u/D_delta).

These sums have at most SIMPLE poles globally because N_0/D_delta and N_u/D_delta are explicitly sums of individual inverse row factors. We do not introduce the unweighted 1/D_delta functional, which could have higher pole order at another component with several coincident row hits. At the good unique hit x*=rho^I,

    Res Y_k=c_I*x*^k, Res Z_k=u_j* c_I*x*^k.       (1)

This is exactly the attractive rank-one moment promise.

Multiplication by D_delta yields a short initialized recurrence

    sum_(l=0)^J d_l(delta)Y_(k+l)=Lambda(X^k*N_0),  (2)

and the corresponding weighted equation. For k=0,...,J−1 the right sides are acquired by Hankel convolution with mu_0,...,mu_(2J−2), costing soft J. No finite-clock mass has been inverted.

## 4. Test whether rank one and these cheap equations determine the ratio

They do not, for this specific attempted closure. Construct a REGULAR particular solution prefix: set Y_0,...,Y_(J−1)=0 and solve (2) forward through 2J−1, and similarly for Z. Because d_J is a unit, the resulting lower-triangular convolution is inverted in soft J at fixed precision. Its pole residue is zero.

Now choose ANY supplied row j and put theta_j(delta)=A_delta/T_j, with a certified unit inverse T_j. For any acquired unit lambda add

    delta^-1*lambda*theta_j(delta)^k   to Y_k,
    delta^-1*lambda*u_j*theta_j(delta)^k to Z_k.   (3)

D_delta(theta_j(delta))=0, so (3) is a homogeneous solution of (2), EXACTLY before truncation. It has only a simple pole and normalized rank-one residue (lambda*T_j^-k, lambda*u_j*T_j^-k). Its first O(J) coefficients are acquired in soft J for any chosen j. Thus the known moment equations, unit pivots, simple-pole promise and common-ratio rank-one condition admit such candidate prefixes for EVERY supplied row tag, not only the actual clock intersection.

These artificial prefixes are not claimed to be another attained native input, nor to prove information-theoretic impossibility. They identify the exact condition omitted by THIS normalized moment recurrence: the finite clock support.

For the actual functional let W_clock(X)=product_(i<h)(X−rho^i). Then exactly

    sum_l [X^l]W_clock *Y_(k+l)=0                  (4)

and likewise for Z, since W_clock vanishes at every actual node. The added homogeneous term (3) has leading residue proportional to W_clock(T_j^-1). Consequently (4) selects precisely the true row in the promised good field. Imposing it by acquiring W_clock modulo D_0 is the old implicit factorial remainder, costing soft(J+sqrt(Jh)); uniqueness does not initialize that remainder in this algorithm.

This execution therefore isolates a genuinely smaller sufficient operation: enforce the finite-clock condition on ONE rank-one modified-moment pole, or acquire just the two first-subresultant coefficients, rather than all modified moments. It does not compute that operation. A q-Pearson/continued-fraction algorithm that enforces (4) more cheaply remains possible, and is not ruled out by (3).

## 5. Cost and conclusion

All short polynomial inputs, first ordinary moments, unit leading coefficient, regular particular prefix and any normalized candidate prefix in (3) are paid in soft K. Their ambiguity is algebraically explicit on the actual supplied coefficients. The first unpaid operation is clock-support selection of that rank-one pole; the completed fallback remains soft K^(5/4).

Conditional GLOBAL uniqueness DOES provide two useful gate-free whole-bin targets: the two first product jets, or the two canonical first-subresultant coefficients followed by short cofactor evaluation. It removes the need to identify an empty block or control cancellation among many amplitudes. It does not by itself let the paid short ordinary moments choose the true pole. No root of unity, hidden order, torus-only tag promise, generic full-resolvent construction or broad algorithmic lower bound is imported.
