
## Terminal boundary solvers: acquired Newton data and exact missing contractions, 2026-10-24

The previous pass acquired both monomial coefficient boundaries of the
actual reciprocal grid in soft k. This pass executes three ways of using
them: a finite adjoint certificate, a geometric Newton boundary transfer,
and a compressed coefficient-system solve. The true upper Newton boundary
is now acquired in soft k, and the first adjoint/transfer steps are paid.
None of the completed algorithms improves the whole-query cost
soft(J+sqrt(JL))=soft k^(3/2). The one-sixth factoring theorem and full
executable/Lean bit-complexity composition remain open.

### Exact initialized system and a lawful dense completion

Retain the actual main length L0=2H=k*(2k), H=k^2, m=k, G=2k, Q=q^k,
and the separately acquired TWO original tail factors. Let F have its
actual native roots y_j, or the acquired reciprocal augmentation using
q^(1-L0). Write j=deg F, D=jG<=4H, and

    A(T)=F(Q^(-(G-1))*T), B(T)=A(Q^G*T),
    R(T)=prod_(g<G) prod_j(T-Q^g*y_j),
    A(T)R(QT)=B(T)R(T).

All generators and the unit constant R0 are actual data. The first and
last O(j) coefficients are also acquired by the earlier power-sum method
at soft k cost. Longer boundary widths are charged, rather than assumed.

The paid rough preparation supplies a stronger unit fact than the written
short-exponent guard alone: every local component order of q is k-rough,
so raising q^n to k preserves whether it is one. Therefore Q^n-1 is a
unit for every 1<=n<=D<=4H<C, including when kn>C. This proves legitimacy
of a needed division; producing all D inverses still costs soft D.
Integers through D are units since both hidden primes exceed16H.

For A=sum a_i T^i and B=sum b_i T^i, b_i=a_i Q^(Gi), the positive
coefficients of R solve the dimension-D triangular system

    a0*(Q^n-1)*r_n
      +sum_(1<=i<=min(j,n-1))(a_i*Q^(n-i)-b_i)*r_(n-i)
          =(b_n-a_n)*R0.

Its right side has only j potentially nonzero entries; its diagonal is
certified unit. A complete fast solve is initialized as follows. Acquire
log(A/a0) through precision D+1, multiply coefficient n by
(Q^(Gn)-1)/(Q^n-1), exponentiate, and multiply by R0. Only formal series
with known unit constants are inverted or logged. This computes the
actual full R in soft D, even when its terminal values are nonunits.
Monic reduction and evaluation at the known P_m roots complete the query
in soft D=soft k^2, slower than the retained blocked algorithm.

The exact desired short output can be written Pi*M^(-1)*b plus the known
R0 contribution, where M is this actual system and
Pi[h,n]=[T^h](T^n mod Phi_m), Phi_m=prod_(i<m)(T-q^(-i)). Pi has an
acquired order-m recurrence/known-root description; its full m-by-D array
is not supplied. A short-output algorithm for THIS contraction remains
the substantive target.

### A finite adjoint cancels cross terms but does not supply the value

With zero extension outside the finite coefficient interval, the exact
adjoint is

    (L* z)_s=sum_(i=0)^j(a_i*Q^s-b_i)*z_(s+i).

For a required point t=q^(-i), 0<=i<m, the actually initialized test
z_s=t^s*(B(Qt)+A(t)*Q^s) cancels its middle term and gives

    A(t)A(Qt)R(Q^2*t)=B(t)B(Qt)R(t).

All four coefficient arrays at all m points are acquired by four degree-j
multipoint evaluations in soft k. This is a zero-safe identity, not a
division by endpoint values. In particular some B endpoints correspond
to negative original indices; no original nonnegative-index consumer is
silently assigned to those auxiliary coefficients. General g-step
transport has an explicit telescoper, but its literal data at all m
points have gm entries.

A separate finite reverse stencil can enforce a requested functional on
the interior coefficients, with its contraction reduced exactly to the
two supplied width-j ends. Its naive trajectory costs O(Dj). The faster
variation-of-constants circuit is

    L_+^(-1)=M_R * Delta_Q^(-1) * M_(BR)^(-1),
    Delta_Q^(-1): f_n -> f_n/(Q^n-1), n>=1.

Every series inverse has unit constant, but both long multiplication
generators still need acquisition. For evaluation lambda_a=t^a, the
first transposed multiplication has the literal entry

    (M_R^t lambda)_s=t^s*(R(t)-sum_(a>D-s) r_a*t^a).

The upper boundary pays the displayed tail for s<=j. It leaves R(t),
the desired value, as the attempted shortcut's missing initialization.
This does not rule out another adjoint circuit; it prevents assuming
that this one was initialized from the boundary data alone.

### The upper Newton boundary is actually cheap

Let x_i=q^(-i), N_d(T)=prod_(i<d)(T-x_i). The exact sparse shift is

    N_k(T)*N_d(QT)=Q^d*N_(d+k)(T),
    T*N_d=N_(d+1)+x_d*N_d.

The desired remainder consists of the first k Newton coefficients of R.
The supplied low monomial coefficients are not those coefficients.
However, its TRUE upper k Newton coefficients can be acquired in soft k.
Put f(w)=w^D R(1/w) mod w^k and b_D(w)=prod_(i<D)(1-x_i*w). Its first
k coefficients follow from geometric-root power sums, using only the
short denominators 1-q^(-r), r<k. Compute U=f/b_D mod w^k. If rho_d are
the Newton coefficients and z_l=x_(D-1-l), reversal gives

    U(w)=sum_(r<k) rho_(D-r)*w^r
                         /prod_(l<r)(1-z_l*w) mod w^k.

Multiply by prod_(l<k-1)(1-z_l*w) and reverse the resulting degree-<k
polynomial. An ordinary length-k Newton basis conversion with reversed
nodes now gives all rho_D,...,rho_(D-k+1) in soft k. No middle coefficient
of R is materialized.

The first actual window transfer is also paid. With v_i=R(x_i),

    F(q^(-(kG+r)))*v_r=F(q^(-r))*v_(k+r).

For 0<=r<k all2k coefficients are acquired in soft k. A denominator
F(q^(-r)) is an ORIGINAL endpoint product: native roots map to index r,
and reciprocal roots map to index L0-1-r. Both are within the original
main interval. Any nonunit is tested and localized with that actual map
before inversion. The numerator is not inverted.
The first Newton pivot is F(1)*N_k(x_k), with the geometric factor a
certified unit. This executes one step without pretending to know the
k initial Newton values.

Continuing through all windows emits Theta(D) multipliers. On the branch
where these divisions are units, matching the k acquired upper Newton
coefficients gives an explicit k-by-k system in the lower amplitudes,
with chain-weighted divided-difference entries. Those entries are not
free; literal assembly already writes k^2 scalars. Outside original
indices no new global-zero coefficient receives an unproved consumer.
The zero-safe dense coefficient solve above remains the universal
completion of this attempted transfer.

The obvious short quotient update also fails explicitly:
P_k(QT) mod P_k is a UNIT, since at x_i its factors have exponents
k+r-i in[1,2k-1]. Thus for h=P_k*u+v the omitted term in h(QT) mod P_k
is P_k(QT)*u(QT), multiplied by a unit. The quotient carry survives;
an enriched state must account for it. This is a specific nonclosure,
not a general recurrence lower bound.

### Structured-solver contracts and scope

The exact gauge inverse factors as Toeplitz(R), the diagonal
1/(Q^n-1), and Toeplitz(1/(BR)). Its middle coefficients remain unpaid.
For the literal lower shift Z and diagonal Lambda=diag(Q^n),
M=T_A*Lambda-T_B satisfies

    MZ-QZM=(Q-1)*Z*T_B.

Because T_B is invertible, this has local rank D-1. The ordinary shift
displacement also has rank D-1. Thus these particular operators do not
give a constant-rank structured solver; other representations remain open.

The inspected primary scalar q-series theorem is nearlinear in precision
D, not in the short input degree j. The ordinary modular-syzygy equation
-B*h+A*g=0 does not enforce g=h(QT): the compatible pairs are not an
ordinary polynomial submodule, since multiplying both entries by T
breaks q-compatibility. The cited approximant-basis theorem cannot supply
that missing constraint or remove its modulus-degree cost automatically.
Exact primary contracts and source fingerprints are retained in the reports.

All completed query versions retain original row, main, reciprocal and
two-factor-tail labels before the original norm/beta consumer. The new
upper Newton data and initialized first steps do not establish the
terminal contraction. Reports, independent exact-source reviews and
validator are in /tmp/semiprime-terminal-boundary-20261024. All prior
shared prefixes, all270 frozen entries and concurrent RH work are preserved.
