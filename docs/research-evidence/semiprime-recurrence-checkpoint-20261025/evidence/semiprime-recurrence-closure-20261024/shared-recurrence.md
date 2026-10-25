# The initialized common fourth-order recurrence and its family product

24 October 2026. Root synthesis, scratch only. This records the scalar
recurrence noticed independently by the two quadratic-constructor agents,
with its exact coefficients, starts, norm recovery and an executed family
extension. It is a paid constant-order recurrence for individual collision
values. It is NOT a soft-k algorithm for their long product.

Source: `frobenius-pairing.md`, SHA256
`215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`,
independently reviewed in `frobenius-pairing-review.md`, SHA256
`147ed84ea489fb61e8e2b47e2c6d09a90cf247f743df017e48314b613f815a97`.
This is the NEW publicly aligned quadratic constructor, not a compressed
claim about the earlier rank-k Gauss vectors.

## 1. Actual scalar sequences, common coefficients, actual starts

Work in B=(Z/N)[tau]/(tau^2-D), with the acquired negative fundamental
discriminant satisfying (D/N)=-1, conjugation bar, and Norm/Tr to Z/N.
The predecessor supplies all actual rank-two targets V_j and unit seed
z=(beta W)^H, H=k^2, in soft k. Set

    t=Norm(z)=beta^(2H), s=Tr(z),
    h_j(i)=Norm(V_j-z^i).

Every h_j is the ACTUAL scalar norm of an original bounded leaf. The
following is an identity in the ring, not a diagonalization assumption:

    h_j(i)=Norm(V_j)+t^i-bar(V_j)*z^i-V_j*bar(z)^i.       (1)

Thus the shift operator E annihilates every h_j under the same polynomial

    C(T)=(T-1)(T-t)(T^2-s*T+t)
        =T^4-A*T^3+B0*T^2-t*A*T+t^2,
    A=1+t+s, B0=2*t+s*(1+t).                            (2)

Indeed each of 1,t,z,bar(z) is a root of this polynomial in B. Applying
the polynomial in the shift to each term in (1) proves the assertion,
and the resulting equality has scalar coefficients and values. Repeated
eigenvalues, nonunit discriminants and vanishing h_j values cause no
exception. No Vandermonde or eigenvector inverse is used.

The explicit recurrence is

    h_j(i+4)=A*h_j(i+3)-B0*h_j(i+2)
               +t*A*h_j(i+1)-t^2*h_j(i).               (3)

Acquire z^0,z^1,z^2,z^3 with three constant-rank multiplications. Compute
the four starts for every j from the actual V_j and the norm formula.
There are O(k) such computations, all on O(log N)-bit residues. Hence the
common coefficients AND ALL row starts cost soft k bits. The last
coefficient t^2 is a certified unit, but forward use of (3) needs no
division at all. A selected index can be reached by polynomial powering
modulo the monic C in O(log(i+1)) constant-size ring steps. This improves
neither the already paid binary-power leaf evaluation nor the long query.

The finite etale quadratic algebra has exactly one unknown nonsplit
local field. Therefore a proper gcd of h_j(i) with N factors N, while a
saturated gcd forces the paired beta equality at that field side. The
predecessor's exact same-leaf identity then gives a factor or the original
bounded beta witness. This recovery applies to the concrete sequence (1),
not an arbitrary order-four recurrence supplied without that structure.

## 2. Execute the recurrence for the whole row product

Acquire the monic F(X)=prod_j(X-V_j)=sum_(a=0)^J f_a X^a over B by the
ordinary product tree, at soft J cost. Repeated targets are allowed. The
column product of (1) is

    g(i)=prod_j h_j(i)=Norm(F(z^i))
        =sum_(a,b=0)^J f_a*bar(f_b)*(z^a*bar(z)^b)^i.    (4)

This is an exact way to extend the common recurrence through the product.
Its coefficients have a compact outer-product description, but (4) has
(J+1)^2 labeled exponential terms before coincident bases are merged.
There is a scalar monic annihilator

    C_J(T)=prod_(a=0)^J (T-t^a)
      *prod_(0<=b<a<=J)
         (T^2-Tr(z^a*bar(z)^b)*T+t^(a+b)).              (5)

Pair (a,b) with (b,a) to prove (5); conjugate bases have sum given by the
trace and product t^(a+b). The displayed polynomial has EXACT formal
degree (J+1)^2 and leading coefficient one, even if some of its factors
coincide after specialization. This is only a supplied annihilator;
the minimal recurrence might be smaller. No lower bound is inferred.

The initialization is fully executable. The trace coefficients satisfy

    Tr(z^a*bar(z)^b)=t^b*Tr(z^(a-b)) for a>b.

Acquire t^b and Tr(z^r), 0<=b,r<=J, in soft J using the quadratic trace
recurrence. Enumerating the factors in (5), and multiplying them by a
product tree, costs soft J^2. The first (J+1)^2 actual g(i) values can be
acquired by monic multipoint evaluation of the known F at the consecutive
z^i, followed by rank-two norms, again in soft J^2. All node acquisition
is charged. This supplies a genuine large recurrence and all starts,
without assuming that the compact coefficient outer product initializes
its expanded recurrence for free.

At J of order k, this costs soft k^2. Computing the target terminal
product prod_(i<L)g(i) is an additional operation; the monic annihilator
does not itself compute that multiplicative functional. Retaining the
factored F and using the prior geometric blocking algorithm is cheaper,
at soft(J+sqrt(JL))=soft k^(3/2), with the already checked norm localization
and saturated leaf recovery. A small linear recurrence for every entry
has therefore not supplied a small acquired state for the product of all
entries. This conclusion concerns the executed extension (4)--(5), not
all possible fused recurrences.

## 3. What the quadratic constructor has and has not changed

All character discovery, rank-two row coordinates, seed unit guards,
scalar recurrence coefficients, starts and original witness recovery
are acquired within soft k. This removes the old need for O(k) expanded
rank-k rows and the old unresolved torus-survival premise for this NEW
family. The original own-tag coverage and length L=2k^2+2 are preserved.

The remaining target is a product algorithm using this actual shared
recurrence/row input whose total cost is soft k, on arbitrary original
row/index restrictions as needed for factor recovery. Neither the scalar
recurrence (3), its expanded family version (5), nor the cheap final norm
constitutes that algorithm. No change of factoring exponent, complete
bit-cost composition or Lean sixth-rate theorem is claimed here.
