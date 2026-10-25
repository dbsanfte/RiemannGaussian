# q-Newton generating function and executed parity-decimation attempt

24 October 2026. Scratch only. No soft-k algorithm obtained. This continues the exact Ore recurrence rather than substituting in a fixed quotient.

Let A be X in R[X]/F, R=Z/NZ. Put (a;q)_n=prod_(r<n)(1-aq^r). For n<=h all (q;q)_n are units by the supplied local order >16H>h. No infinite series denominators beyond that range are used below.

## 1. Implicit vector initial data and scalar rational input

Define, only to the required precision,

    G_q(z,A)=sum_(n>=0) (A;q)_n/(q;q)_n z^n.

It is uniquely specified through degree h by G(0)=1 and

    (1-Az)G(qz)=(1-z)G(z).

The usual notation (Az;q)_infinity/(z;q)_infinity is shorthand for this normalized solution; no convergence of infinite products in the finite ring is assumed. The desired remainder is (q;q)_h [z^h]G. Its initial datum is just 1 in the monic quotient, so no J-by-J initial remainder array is required.

For any supplied linear functional ell on this quotient, put u_r=ell(A^r). Its ordinary generating function is rational:

    U(w)=ell((1-wA)^(-1))=B(w)/F_rev(w),
    F_rev(w)=w^J F(1/w), deg B<J.

The first J u_r are precisely the supplied coefficient-basis entries of ell, since A^r=X^r for r<J. Thus B is acquired in soft J by one convolution with F_rev, truncated modulo w^J; no modular-composition primitive is needed. The requested scalar is exactly

    ell((A;q)_h)=sum_(r=0)^h
      (-1)^r q^(r(r-1)/2) [h choose r]_q u_r.

Thus a weak scalar selector has a genuine degree-J rational input U, but its requested output is a q-binomial transform, not the ordinary h-th coefficient of U.

Indeed, writing e_q(z)=sum z^n/(q;q)_n and

    V(z)=sum u_r (-1)^r q^(r(r-1)/2) z^r/(q;q)_r,

one has ell(G_q(z,A))=e_q(z)V(z). The q-Borel weighting turns the rational U into V; no degree-J rational representation of V was established. Ordinary rational Bostan-Mori on U computes u_h rather than the requested transformed coefficient.

## 2. A true norm identity that resembles Bostan-Mori

The normalized solution satisfies, through the usable precision,

    G_q(z,A) G_q(-z,A)=G_(q^2)(z^2,A^2).             (1)

Proof: the left side has constant term 1 and, under z->qz, is multiplied by (1-z^2)/(1-A^2z^2); its odd coefficients vanish. The coefficient uniqueness for base q^2 proves (1). The local orders of q are odd, so q^2 retains the same order. The identity therefore survives all required denominator checks.

The quotient can also change exactly. The polynomial

    F_square(Y)=prod_j(Y-x_j^2)

is acquired in soft J from the even polynomial (-1)^J F(X)F(-X). Mapping A to A^2 is lawful into the corresponding monic quotient. If it is necessary to recover A from A^2, the actual target roots lie in the odd-order subgroup locally, so a target cannot be minus another target. Thus F(X),F(-X) have unit resultant. Writing F(X)=F_even(X^2)+X F_odd(X^2), the polynomial F_odd is a unit modulo F_square and

    A=-F_even(A^2)/F_odd(A^2).

This gives an acquired soft-J transport after unit checks/Euclidean inversion; repeated original roots do not invalidate the no-plus/minus argument. Hence (1) does not fail because of an unacquired quotient conversion.

## 3. The parity numerator does not stay polynomial

Unlike rational Bostan-Mori, (1) does not supply the selected parity section: multiplication by G_q(-z,A) is multiplication by another long series, rather than by a known degree-J polynomial denominator. For example,

    G_q(z,A)=G_(q^2)(z^2,A^2)/G_q(-z,A),

and 1/G_q(-z,A)=G_q(-Az,A^(-1)); this is another normalized q-series, not a short polynomial. A is a unit because all acquired target roots are units.

Executing coefficient decimation explicitly makes the residual visible. The even section is

    sum_(n>=0)
      (A;q^2)_n (Aq;q^2)_n
       /[(q;q^2)_n (q^2;q^2)_n] w^n,

and the odd section is

    (1-A)/(1-q) * sum_(n>=0)
      (Aq;q^2)_n (Aq^2;q^2)_n
       /[(q^3;q^2)_n (q^2;q^2)_n] w^n.

The normalized one-numerator/one-denominator kernel has become a two-numerator/two-denominator kernel. After d successive parity sections, with B=2^d and selected residue 0<=r<B, it is exactly

    (A;q)_r/(q;q)_r *
    sum_(n>=0)
       prod_(s=0)^(B-1)(A q^(r+s);q^B)_n
       /prod_(s=0)^(B-1)(q^(r+1+s);q^B)_n w^n.   (2)

This includes the vector initial value implicitly and correctly. Acquiring the A-dependent degree-B seed product costs soft B before reduction, or soft(J+B) with a block strategy; acquiring every coefficient of a general reduced multistep transition is not provided by the norm identity.

The numerator of (2) at its next coefficient is precisely a shifted length-B q-product in A. Thus this executed decimation moves the original operation into the growing seed instead of turning it into constant-cost quotient arithmetic. At B approximately h it asks for (A;q)_h again. Keeping B small leaves approximately h/B coefficient steps; direct quotient multiplication is at least the cost of this concrete B-block execution, and using the existing shared target block evaluator returns soft(B+Jh/B+J), optimized at sqrt(Jh). No implicit contraction of the growing parameter product was obtained.

## Exact residual

The normalized generating function solves implicit vector initial data, and its parity norm permits actual soft-J quotient changes. The still-unpaid operation is extracting one parity section while representing its growing q-hypergeometric seed in soft J space with soft-J total advancement cost. Formula (2) identifies that seed exactly. Neither the rational moment series nor the norm identity supplies a degree-J rational fraction whose ordinary h-th coefficient is the desired q-Newton transform. This is a failed concrete candidate, not a lower bound against another algorithm.
