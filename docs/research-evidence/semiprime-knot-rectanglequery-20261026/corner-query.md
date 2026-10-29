# Execute the corner cancellation on the acquired Cartesian query

26 October 2026. Parent finite calculation. The new Gauss-basis family
really supplies a Cartesian product, so the finite rectangle identity
can now be applied with actual parameters. Its naive specialization is
universally 0=0; regularization leaves three other unacquired bulk
products. This is a failure of that specific proposed direct readout,
not a lower bound on further recursive or joint contractions.

The concurrent string-theory proposal suggested this calculation and
was read without modification. The relevant primary motivation is
[Nekrasov, equations (127), (128), and (198)](https://arxiv.org/html/1512.05388).
Those formulas express the specified gauge-theory observables through
partition boundaries. The finite arithmetic calculation below is
derived directly and imports no gauge-theory averaging theorem.

## 1. The exact finite input, including its hole

For one retained cell write a=A-1, b=B-1, Q=q^(-1), and M=4k.
The acquired X,Y are units. Define finite polynomials

    F(z)=product_(r=-a..a,s=-b..b,h=0..M)
                          (1-z*X^r*Y^s*Q^h),
    H0(z)=product_(h=0..M)(1-z*Q^h),
    P(z)=product_(r=-a..a,s=-b..b,(r,s)!=(0,0),h=0..M)
                          (1-z*X^r*Y^s*Q^h).

Thus F=H0*P is a polynomial factorization, and P(1) is the actual
cell target. It is NOT computed by dividing F(1) by H0(1), since
H0(1)=0. All powers are finite; no analytic convergence is used.

Introduce corner polynomials

    Cplus(z)=H0(z*X^(-a)*Y^(-b))
             *H0(z*X^(a+1)*Y^(b+1)),
    Cminus(z)=H0(z*X^(a+1)*Y^(-b))
              *H0(z*X^(-a)*Y^(b+1)).

Direct cancellation of matching FORMAL factors gives the cleared
polynomial identity

    P(z)*P(XYz)*Cminus(z)*H0(z)*H0(XYz)
       =P(Xz)*P(Yz)*Cplus(z)*H0(Xz)*H0(Yz).        (1)

It follows by first telescoping F(z)F(XYz) against F(Xz)F(Yz),
then inserting F=H0*P and cancelling common polynomial factors in
the formal Laurent polynomial ring. Equation (1) specializes over
the native composite ring without numerical division. The hole
contributes the four H0 factors; omitting them changes the target.

## 2. Why the naive endpoint is identically uninformative

For these grids A,B>=2. One way to verify this is to combine
ell1>=sqrt(2N) with ell1*ell2<=2kN/sqrt3, obtaining
ell2<=sqrt(2/3)*k*sqrtN<R=2k*sqrtN.

At z=1, the factor H0(z) on the left vanishes identically. Also
P(X) has the included factor indexed by (r,s,h)=(-1,0,0), which
equals 1-X*X^(-1)=0. P(Y) similarly has the factor (0,-1,0).
Therefore evaluating (1) at the requested endpoint gives 0=0 on
EVERY native input. This conclusion does not depend on an accidental
modular alias or on the location of the unknown useful collision.

These zeros belong to the translated auxiliary products, not to
invalid original leaves of P(1). The original public filter remains
valid. It cannot make the newly translated tautologies invertible.

Formal regularization does not by itself acquire P(1). Factor out
1-z from H0(z), P(Xz), and P(Yz), and from P(XYz), whose included
index (-1,-1,0) supplies the same factor. Both sides of (1) have
the two displayed copies. Cancelling those copies FORMALLY yields
a valid relation at z=1 involving P(1), the three remaining
regularized bulk products, and boundary factors. Those bulk
products have not been evaluated by acquiring their corner data.
Additional coincidences, if any, must still be treated by finite
gcds and their integer labels; no numerical zero is divided out.

## 3. The boundary strings themselves can be paid

There are only eight displayed H0 strings per cell. For every such
string its start is an acquired short power beta^L. Each individual
factor has label L-Hh with 0<=h<=M. If one label is literally zero,
identify that integer index directly and omit it BEFORE evaluation,
splitting the interval into at most two strings. An identically
constant start is handled the same way. All remaining factors have
nonzero O(logN)-bit labels and therefore the existing proper-gcd or
saturated-annihilator decoder.

There are soft O(k) resulting string starts across the whole family,
with a common clock and length O(k). The inherited monic geometric
product engine acquires their products and localizes any nonunit
in soft O(k), including at most one terminating T_ext. Prefix/tail
splits add only a constant number of common interval groups per
start; arbitrary endpoints can instead be handled by a logarithmic
dyadic decomposition, preserving the soft bound. This is an actual
cheap boundary screen, not a claim that it contains a guaranteed
useful zero. If it finds none, it certifies the remaining displayed
boundary factors are units and leaves the regularized bulk products
unknown.

## Outcome

The exact Cartesian specialization and its zero accounting have
been executed. The boundary data can be acquired within the budget,
but the direct cleared identity specializes to a universal tautology.
Its regularized version still requires bulk initial values. Neither
the finite identity nor the literature theorem supplies a coverage
theorem for the boundary screen or an initialized short system for
those bulk values. The original complete query bound is unchanged.
