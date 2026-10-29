# Independent review: joint Lambert contractions and public-label determinant

26 October 2026. Paper-only formula, consumer and prior-source audit. No numerical tests, code or repository changes. **PASS with one explicit prefactor correction in joint-lambert §3.** The proposed public-label row-value determinant is valid, but its long input remains unacquired.

## 1. Existing report: finite kernel and quadrature error

The moment formula mu_t=(rho^{t+1};rho)_{h-1} and its recurrence mu_{t+1}/mu_t=(1-rho^{h+t})/(1-rho^{t+1}) are correct. The finite native horizon plus O(sqrt K) moment range stays within the actual short-unit margin; numerator factors need not be inverted merely to generate the recurrence. The formal error decomposition (A) follows by splitting Q(z)=Q(X)+(Q(z)-Q(X)), and remains valid after clearing Q without a Hankel pivot assumption.

**Correction:** for C(z)=sum_i c_i/(z-x_i) and z_j(delta)=(1+delta)/T_j, the ORIGINAL regulated row sum is

    sum_i c_i/(1+delta-T_j*x_i)
       = T_j^{-1} C(z_j(delta)).

Therefore §3's evaluation of P/Q and the error at z_j must include the known unit T_j^{-1}. As written without it, their delta-residue is T_j*c_I, not c_I. This does not invalidate the singleton-block consumer because the extra amplitude is a unit, but it changes the exact requested Lambert formula. With that prefactor restored, a Q unit at a hit makes the approximant regular and leaves precisely c_I in the error term.

The simultaneous-remainder completion is valid with the stated reciprocal-root conventions: reverse each denominator product to the actual monic root polynomial product(X-T_j), acquire G_h and its derivative there, and evaluate by monic remainder trees. Repeated T_j values need no inverse derivative of their row polynomial. A globally zero row has one clock hit per component and hence unit G_h'(T_j). This justifies the exact Lambert baseline and empty-block zeros at the old soft(J+sqrt(Jh)) cost. No new selected-gcd or quadrature acquisition follows.

## 2. New proposed row-value determinant: exact singleton output

For an original sign-invariant block let R_j=G_h(T_j) and define

    D_b(delta,epsilon)=product_(j in b)(R_j+delta+epsilon*w_j).

Write D0=D_b(0,0), Ddelta=[delta]D_b and Depsilon=[epsilon]D_b. At the good nonsplit field an EMPTY block has D0!=0. A block with its unique leaf hit has precisely one zero row R_j*, because one clock hit per row is guarded. Thus

    D0=0, Ddelta=A=product_(j!=j*)R_j!=0,
    Depsilon=A*w_j*.

Canonical w_j*=[R²]_n is the current bounded integer weight. This is a legitimate arbitrary-unit-amplitude weak pair after a mandatory D0 zero gate. It is not the Lambert pair numerically and is not claimed to be; singleton coverage makes both valid outputs.

Without that zero gate an empty block could have nonzero derivatives and an irrelevant ratio. The gate is mathematically essential.

## 3. Composite/split-component gate and one attempt per bin

Compute g0=gcd(N,Norm(D0)). A proper gcd factors. If g0=1, skip the block. If g0=N, apply coordinate gcds to D0. Any proper coordinate gcd factors; otherwise D0 is globally zero. Indeed a norm zero at a split prime may initially mean only one split coordinate is zero, but a nonzero algebra value there has a nonzero coefficient and produces the proper coordinate gcd when the good nonsplit component is zero. More generally, if both norm and coordinates are saturated, the value itself is zero. Do not identify saturated norm alone with a global zero for this arbitrary D0.

On the global-zero branch test Norm(Ddelta). A proper gcd factors, a unit norm licenses inversion, and a saturated norm permits declining the block. In a correct bin a hitting block has nonzero A at the good field, so it cannot be lost to that saturated-norm decline. Empty correct-bin blocks cannot pass the global-zero gate. Consequently any accepted unit-derivative block in that bin has the correct ratio Depsilon/Ddelta. The usual tau-coordinate test, ONE bounded scalar scan and squared-tag HH menu apply; there is no need to test every block's candidates through HH. Wrong-bin failures are bounded and do not suppress the correct bin.

This reasoning explicitly allows multiple hits or degeneracies in other components. They either expose a proper gcd or yield a saturated derivative on an unpromised attempt; no false local-to-global uniqueness is assumed.

## 4. Public-label algebra and exact resultant

Let F_b(X)=product_(j in b)(X-j), with distinct canonical integer labels j in [1,K). Every nonzero j-j' has absolute value less than K<P,Q, so it is a scalar unit modulo N and hence a unit in B. The label algebra B[X]/F_b is therefore the actual split product B^{|b|}, independently of repeated or colliding numeric T_j.

Fast monic product trees and interpolation acquire Y_b(j)=T_j and W_b(j)=w_j in total soft K. Their inverses are only public label differences; no native collision factor is inverted. The exact formula is

    D_b(delta,epsilon)
       =Res_X(F_b(X), H_b(X)+delta+epsilon*W_b(X)),
    H_b=G_h(Y_b(X)) mod F_b.

F_b is monic, so the resultant is exactly the product of the displayed values, without an omitted sign or leading coefficient. It remains a polynomial identity over the actual ring, including repeated T_j and zeros. Once H_b is supplied, MPE back to the public labels followed by a constant-rank product/derivative tree acquires D0,Ddelta,Depsilon in soft |b|, without a generic unit-pivot determinant oracle.

The first unpaid quantity is H_b. Its actual values ARE G_h(T_j). The public-label quotient permits composition at repeated numeric roots, but does not compute that long composition cheaply. Joint evaluation by the inherited row engine plus interpolation pays it at soft(K^{5/4}); materializing the degree-h G_h or evaluating each labelled block separately is not a soft-K substitute.

## 5. Narrow prior-credit search

The public-metadata algebra is explicitly old. The [23 October norm-detector §3](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-detector-acquisition-20261023/reports/norm-detector.md) constructs a split row algebra by interpolating at distinct small INTEGER metadata nodes, whose differences are units under the small-factor prefix, while retaining all original numeric row values. Thus avoiding separation of T_j via public labels is not a new construction.

The [24 October diagonal-product §§2–3](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-zero-query-20261024/diagonal-product.md) already uses an acquired labelled finite algebra, exact matched selection and its norm to preserve the desired scalar, explicitly charging its implicit modular composition. That instance uses separated native roots as labels, whereas the Oct23 metadata construction already supplies the repeated-root-safe alternative.

The new useful application is the present singleton-block row-value perturbation together with its explicit empty-block gate and fixed-depth derivative pair. It simplifies the output specification on the current complete bank. It is not a new generic interpolation/resultant algorithm, and no acquisition or exponent gain has been established.

**Disposition:** accept the proposed gate, fixed-depth row-value derivative pair and public-label resultant, including split-component handling. Restore T_j^{-1} in the report's quadrature pullback for exact Lambert equality. The long H_b composition remains the actual unpaid operation.

## 6. Positive implementation simplification: only row values, no clock derivative

The row-value perturbation is cheaper to IMPLEMENT after the long query than the exact Lambert normalization. Acquire only A_j=G_h(T_j), then multiply the tuples

    (A_j,1,w_j)

inside the constant-rank ring B[delta,epsilon]/(delta²,delta*epsilon,epsilon²). Tuple multiplication is

    (a,b,c)*(d,e,f)=(ad, ae+bd, af+cd).

The product is exactly (D0,Ddelta,Depsilon). All operations are additions and multiplications, including at zero divisors. Total cost over the original block partition is soft K, with no G_h' evaluation, no q-binomial c_i array, no kappa normalization and no individual native-root separation. The gate in §3 is still mandatory.

Thus the inherited value-only row engine plus this fixed three-coordinate accumulation completes the new weak block target at the same soft(K^{5/4}) exponent, removing auxiliary derivative/normalizer acquisition from THAT baseline. It is a positive interface/implementation simplification, not a speedup of the long query. The Oct23 metadata-algebra source in §5 retains prior credit, and the actual label-resultant wrapper does not make the missing G_h(Y_b) composition free.
