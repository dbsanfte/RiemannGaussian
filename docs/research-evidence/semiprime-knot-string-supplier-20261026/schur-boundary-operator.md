# An acquired Schur boundary operator for the covered kernel query

26 October 2026. Primary-agent finite derivation, prompted by packages C/E
of the new string-theory research proposal. No numerical experiments or
factoring implementation. The companion cyclic-reciprocity report derives
the same Schur specialization and its determinant; this note supplies a
fully paid inverse action and explains its exact information contract.

**Result:** the boundary matrix, its determinant and its inverse action
are all acquired within soft O(k), including lawful factor-or-unit
screens. Its exact determinant is a product of short boundary factors.
The collision information is in a separate diagonal of long products.
The construction therefore gives a concrete finite string-theory model
and an initialized operator, but no new query exponent.

## 1. Covered input and positive block

Use the prepared universal kernel from the hybrid audit, with
H=k^2, q=beta^H, C=ceil(N/(2k)), V=O(sqrt k), and
W=O(sqrt(N/k)+sqrt k). Its punctured signed product is guaranteed
nonunit. The involution (b,h)->(-b,-h) preserves the nonunit predicate.
Its folded query is the product of

    A0=product_(h=1)^W (1-q^h)

and the positive-b block

    Z=product_(b=0)^(r-1) product_(t=1)^s
                                      (1-q^(A+C*b+t)),
    r=V, s=2W+1, A=C-W-1, n=r+s.

Here A>r in the native hard branch. One conservative verification is to
put x=sqrt(N/k)>16*k^(3/2). The explicit bounds in kernel-cover give
D0<=2*k*x, V<3*sqrt k,
T<=x/(8*k^2)+1+3*sqrt k and W<3*x for k>=6. Then
C>=x^2/2>W+V+1. Thus the only literal zero in the signed rectangle is
(b,h)=(0,0); Z has none, and all exponents below are positive except
specified short algebraic interpolation factors.

A0 has a valid soft O(sqrt W) evaluator and recovery, but this is NOT
a soft-k prepass in the hardest regime. Do not infer that Z alone is
covered without handling A0. The construction below costs soft k for
Z's boundary regardless of whether A0 has been evaluated.

## 2. Exact Schur specialization

Take the partition

    lambda_i=A+(C-1)*(r-i), 1<=i<=r,
    lambda_i=0, r<i<=n,
    eta=sum_(i=1)^r (i-1)*lambda_i.

The cross-block factors in its Weyl principal specialization are exactly
the factors of Z. Put

    D=(q;q)_(n-1),
    d_ij=A+C*(r-i)-r+j,
    J_ij=h_(d_ij)(1,q,...,q^(n-1)).

The Gaussian polynomial identity gives, over the formal integer
polynomial ring,

    D*J_ij=product_(t=1)^(n-1)(1-q^(d_ij+t)).

Let x_i=q^(A+C*(r-i)) and define degree-(r-1) polynomials

    P_j(X)=product_(u=-r+j+1)^0(1-X*q^u)
                      *product_(v=1)^(j-1)(1-X*q^(s+v)),
    U_ij=P_j(x_i),
    Z_i=product_(t=1)^s(1-x_i*q^t).

Direct interval intersection gives the exact cleared matrix identity

    D*J=diag(Z_1,...,Z_r)*U.                       (1)

Negative powers in P_j are powers of the supplied unit q. No Z_i or D
is inverted. Jacobi--Trudi identifies det J with the Schur polynomial.

## 3. The long denominator cancels from the boundary determinant

Define V_m(q)=product_(d=1)^(m-1)(1-q^d)^(m-d).
Weyl specialization and (1), first in a universal fraction field, give

    det U=D^r*q^eta*V_r(q^C)*V_s(q)/V_(r+s)(q).

Every ordinary q-factor below s cancels. The resulting POLYNOMIAL
identity is

    det U=q^eta
         *product_(d=1)^(r-1)(1-q^(C*d))^(r-d)
         *product_(t=1)^(r-1)(1-q^(s+t))^t.         (2)

Since both sides are Laurent polynomials over the integers, the identity
specializes over every ring with q a unit, through all collisions. Its
proof does not divide the specialized target Z or the possibly nonunit D.
For r=2 this reads q^A*(1-q^C)*(1-q^(s+1)), directly checked by the
two-by-two determinant.

Equation (2) improves the unit ledger for this concrete specialization:
there is NO need to screen every q-factor through n-1 to initialize or
invert U. Screen only C*d and s+t for 1<=d,t<r. Each is a public nonzero
O(log N)-bit exponent. A nonunit q^ell-1 yields a proper gcd, or a
global beta-annihilator H*ell accepted by the inherited once-only
soft O(N^(31/192)) extractor. The screen uses O(r) short powers/gcds.
On its continuing branch det U is a certified unit.

All r-by-r entries are acquired with O(r^2) ring work: for each row,
form the r-1 left and r-1 right boundary factors, then their prefix and
suffix products. This construction uses no division, even if an entry
vanishes. The determinant value itself is acquired directly from (2)
with O(r) short powers. Both fit soft O(k), with bit costs and one
possible terminating extraction included.

## 4. An actual inverse-action algorithm within the same budget

Given an acquired vector y, compute c with U*c=y as follows.

1. Interpolate the unique degree-less-than-r polynomial f with
   f(x_i)=y_i. The x_i are distinct with unit differences on the screen's
   continuing branch: each difference is a monomial unit times
   1-q^(C*d), 0<d<r. Ordinary divided differences and coefficient
   conversion cost O(r^2) ring operations. All inverses are certified.
2. Evaluate f at q^t for 0<=t<r in O(r^2) ring operations. These nodes
   have unit differences by the original short q-order guard.
3. Recover c_j in descending j using

       f(q^t)=sum_j c_j*P_j(q^t).

   For j<r-t, P_j(q^t)=0 identically. The diagonal entry at j=r-t is

       P_(r-t)(q^t)
          =product_(a=1)^t(1-q^a)
             *product_(a=s+t+1)^(s+r-1)(1-q^a).    (3)

   Every factor in (3) is a unit: the first group is short and the
   second was screened in Section 3. For each t all P_j(q^t) can be
   formed from two prefix/suffix arrays in O(r) operations, retaining
   their exact zero factors. Back substitution therefore costs O(r^2).

This is a complete soft-O(k) inverse ACTION. It does not claim to
materialize the dense inverse in that time or invoke a cubic dense
elimination algorithm. All integers used in powering have O(log N)
bits. No unknown factor, order, root or target value is an input.

## 5. Exact remaining information

Let K=D*J denote the cleared Schur matrix. On the continuing branch,

    K*U^(-1)=diag(Z_i),
    det K=Z*det U.

Thus K has exactly the desired nonunit determinant predicate for the
positive block. The normalization and inverse operation are genuinely
paid. But the entries of K are still the long products in (1); they
have not become acquired by specifying U. Multiplying by U inverse
exposes the same unknown diagonal, and taking a derivative of U alone
does not differentiate those Z_i.

This sharply separates the constructive gain from the outstanding
task. The string-theory specialization supplies an actual initialized,
invertible boundary operator with a cheap determinant. It does not
give the singularity bit of the cleared Schur matrix, a useful residue
of h, or the complete signed query at soft k. A0 and its cost also
remain part of full coverage. The retained original route is still
soft k^(5/4); the current complete universal-kernel readout is still
soft N^(1/4). No new factoring exponent or formal proof is claimed.

## Sources and scope

The proposal's finite Schur and spectral-duality packages motivated
this specialization. Its required integer identities are the usual
Weyl principal specialization, Jacobi--Trudi, and the finite Gaussian
formula for complete homogeneous polynomials. The explicit partition,
boundary matrix, determinant cancellation, unit ledger and inverse
algorithm above are derived here. The companion report records the
checked primary topological-string sources and their normalization
scope; none supplies a semiprime acquisition theorem.
