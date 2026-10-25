# Exact varying-quotient tree and an acquired Ore recurrence

24 October 2026. Scratch only; no shared/frozen edits. No soft-k completion is claimed.

Inputs: R=Z/NZ, unit q with both local orders >16H; monic F(X)=sum_(m=0)^J f_m X^m acquired in soft J; P_t(X)=prod_(0<=i<t)(1-q^i X). The target is P_h mod F, J=soft k and h=Theta(k^(3/2)).

## 1. Exact varying-quotient transport and a concrete sharing attempt

Define monic F_s(X)=q^(sJ) F(q^(-s)X). Its roots are q^s x_j. If R_(t,s)=P_t mod F_s, then

    P_(2t) mod F_s
      = R_(t,s)(X) R_(t,s+t)(q^t X) mod F_s.

Indeed F_(s+t)(q^t X)=q^(tJ) F_s(X). This transports the quotient exactly, with no fixed-quotient substitution.

A natural sharing algorithm at block length t is to acquire G_t=prod_(0<=g<B) F_(gt), B=ceil(h/t), divide the common P_t by G_t once, and propagate remainders down the monic product tree. There are B degree-J moduli. Each F_(gt) can be acquired by scaling its J coefficients along a geometric walk, so the actual acquired coefficient count is Theta(JB); building the tree costs soft(JB). Acquiring the common P_t costs soft t. Total is

    soft(t+Jh/t+J),

minimized at t about sqrt(Jh), exactly the existing soft sqrt(Jh) scale. A residual block is handled separately.

In a dyadic varying-quotient tree, one can stop at a common t-level and share P_t, rather than rebuilding it at every node. The same acquired G_t has degree JB. Refining below this level does not by itself remove its acquisition cost; stopping only once t<=J gives cost soft h. These are costs of this concrete tree, not a lower bound for implicit quotient families. The F_s have short shared descriptions, so an implicit remainder mechanism might bypass G_t; this attempt does not provide it.

## 2. A real annihilating recurrence of order J

Let S be forward shift on a sequence v_t and let z act as multiplication by q^t. Thus Sz=qzS. Put

    D=z^(-1)(1-S).

For the R[X]/F-valued sequence v_t=P_t(X) mod F,

    Dv_t = X v_t,
    F(D)v=0.

This is exact even with repeated roots or nonunit target differences, since multiplication by X in the monic quotient is lawful. It gives an acquired factored Ore-operator description of length O(J). Moreover

    D^m = z^(-m) prod_(r=0)^(m-1)(1-q^(-r)S),

so clearing z denominators yields the explicit order-J recurrence

    sum_(m=0)^J f_m z^(J-m)
        prod_(r=0)^(m-1)(1-q^(-r)S) v = 0.

The coefficient of S^J is the unit (-1)^J q^(-J(J-1)/2). Consequently forward advancement is well-defined without any new nonunit inversions. All starting v_0,...,v_(J-1) can be computed as degree-<J polynomials, but writing that full array already costs J^2 coefficients; the factored initial description remains short.

## 3. One recurrence row can actually be acquired in soft J

Write Q=q^(-1), and A_m=prod_(r=1)^m(1-Q^r). On the asymptotic range J<16H, every A_m is a unit by the supplied local order bounds. They and inverses can be acquired in soft J. (If J exceeds that threshold on a finite input, this particular unit-based transform is not claimed.) The coefficient c_a(z) of S^a in the cleared recurrence is

    c_a(z)=(-1)^a Q^(a(a-1)/2)/A_a
       * sum_(m=a)^J f_m z^(J-m) A_m/A_(m-a).

For fixed supplied unit z, all c_a(z) are a reversed convolution of f_m z^(J-m) A_m with 1/A_r, followed by unit scalings. Hence an entire recurrence row at one t costs soft J, rather than expanding a J-by-J coefficient table. This uses actual acquired factorials and one polynomial convolution. The annihilating recurrence therefore has a short description AND a paid fast one-row coefficient oracle.

## 4. Precise residual

An order-J recurrence with this soft-J row oracle has not supplied v_h in soft J. Advancing it literally requires preceding sequence values; those are the P_t remainders being sought. Unlike a constant-coefficient recurrence, its coefficients depend on z=q^t. A claim to use X^h modulo one characteristic polynomial would replace this changing recurrence by an unproved fixed endomorphism. Binary products of the first-order factors return to P_t(X) at scaled arguments, hence to the varying quotient tree in Section 1.

There may be a fast algorithm for this specially factored Ore recurrence or its transposed weak selector. The concrete missing operation is: advance F(z^(-1)(1-S)) through h steps, from factored initial data, in soft(J+sqrt h) or soft J cost, without materializing J^2 recurrence data or the degree-Jh/t quotient product. No such operation was established here. The recurrence and convolution oracle are exact, but do not prove the requested soft-k locator.

## 5. Scalar initialization is actually soft J

Correction to the vector-array concern: it is not an initialization obstacle for the clean scalar recurrence. Let L be any supplied coefficient-basis functional on R[X]/F, with mu_r=L(X^r), 0<=r<J. These are exactly its J supplied coefficients. For v_t=L(P_t) and Delta_t=prod_(r=1)^t(1-q^r), the q-binomial theorem gives, for t<J,

    v_t/Delta_t = sum_(r=0)^t
      [(-1)^r q^(r(r-1)/2) mu_r/Delta_r]
      * [1/Delta_(t-r)].

Every denominator here is a certified unit when J<16H. One convolution therefore acquires all scalar v_0,...,v_(J-1) in soft J. No J^2 vector initial array is necessary. The Ore recurrence and its fast row oracle thus have fully paid scalar initial data.

If an eventual fast scalar advancement circuit is linear in the mu_r and every division depends only on F,q (and certified unit data independent of mu), algebraic transposition of that circuit can return all coefficients of P_h mod F at comparable cost. A data-dependent branch or inversion involving mu would need separate justification. No fast advancement circuit is provided here; the gap is scalar advancement itself, not scalar initialization.
