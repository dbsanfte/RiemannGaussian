# Direct connection from the packed residue to the two-geometric norm

26 October 2026. Root derivation for this packet. This connects the original
six-domain target to the new compact input without claiming that a different
regularizer, unique-hit promise, or output is numerically identical to it.

Let the original normalized leaves be

    a_ji=1-T_j*q^(-i), 0<=i<h,
    C=[delta^-1] sum_(j,i) w_j/(delta+a_ji).

Here w_j are the original packed weights; repeated rows and multiple hits
are permitted. Put

    D(Y)=prod_j(Y-T_j),
    A_w(Y)=sum_j w_j*prod_(k!=j)(Y-T_k).

Both polynomials are acquired in soft J, including multiplicities. At a
product-tree merge the weighted companion is A_left*D_right+D_left*A_right;
at a leaf it is w_j. No row separation or inverse D'(T_j) is required.

Work to first order in epsilon, and keep delta as an indeterminate. The
compact polynomial

    E_delta,epsilon(X)
      =D((1+delta)*X)+epsilon*X*A_w((1+delta)*X)
      =prod_j((1+delta+epsilon*w_j)*X-T_j) mod epsilon²

has an acquired description of soft J size; this does NOT mean its dense
bivariate coefficient array has that size. Its finite clock product is

    Q(delta,epsilon)=prod_(i<h) E_delta,epsilon(q^i)
      =q^(J*h*(h-1)/2)*prod_(j,i)(delta+a_ji+epsilon*w_j).

Consequently the exact original target is

    C=[delta^-1] (partial_epsilon Q(delta,0))/Q(delta,0).       (1)

This is a componentwise rational-function/Laurent identity. It is not a
licensed inversion of a nonunit constant coefficient over the native
quadratic algebra. The displayed q power is independent of both sources and
cancels from the logarithmic derivative. Each zero leaf contributes exactly
its weight, including repeated roots; each nonzero leaf contributes no pole.

For b>=1, c=floor(h/b), define the actually acquired geometric polynomials

    B_b(Z)=prod_(u<b)(Z-q^u),
    G_c(S)=prod_(v<c)(S-q^(bv)).

Then the SAME Q in (1), with its exact normalization, is

    Res_S(G_c(S), Res_Z(B_b(Z),E_delta,epsilon(SZ)))
      *prod_(bc<=i<h) E_delta,epsilon(q^i).                     (2)

Both resultants have split monic first arguments, so this equality is valid
over the composite ring, with no field pivot or hidden leading factor.
Taking b=ceil(sqrt(h)) gives compact norm inputs of size soft(J+sqrt(h)).
The formal tail also has an acquired product-circuit description of that
size. Acquiring its full delta coefficient expansion or selected Laurent
coefficient is a separate operation; neither is hidden in this input bound.

The benefit is a precise place to seek cancellation: contract the TWO
geometric factors against the acquired pair (D,A_w), while preserving only
the selected logarithmic pole. One need not ask for the full resolvent or
for all norm coefficients. No algorithm completing that contraction in the
input-size bound is supplied here.

The retuned unique family permits a stronger output reduction, proved in
separated-recurrence.md: replace the original packed-count problem by two
physical first variations, whose ratio is the actual row index at its unique
good hit. Those variations are a constant-rank jet computation without the
delta Laurent extraction. This uses a NEW COVERED FAMILY and its inherited
consumer; it is not an equality between the original C and that ratio. For
the original family with several hits, the first derivative of the product
at delta=0 may vanish, so that unique-hit shortcut cannot simply be imported.

The direct formulas (1)–(2) retain the original target for a future fused
norm/residue algorithm; the unique-family interface is currently the smaller
sufficient-output target for such an algorithm. Neither establishes a faster completed
query or a general lower bound.
