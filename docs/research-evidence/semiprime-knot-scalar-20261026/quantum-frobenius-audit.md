# Quantum Frobenius cancellation: applicable operation and missing norm

26 October 2026. Primary-source follow-up to the knot search. This source
adds a precise cancellation mechanism to the literature map; it does not
provide the required scalar-prefix algorithm.

## Source and parameter contract

Vijay Higgins, *Miraculous cancellations and the quantum Frobenius for
SL3 skein modules*, [arXiv:2409.00351v1](https://arxiv.org/html/2409.00351v1),
Theorems 1.1–1.2, 2.2 and Section 4.2; published in IMRN (2025),
[doi:10.1093/imrn/rnaf226](https://doi.org/10.1093/imrn/rnaf226).

The paper constructs a skein-module Frobenius map by threading power-sum
polynomials. For SL3, its theorem assumes that a chosen cube root of the
quantum parameter has exact order r coprime to 6. The images are central
in the surface skein algebra. The quantum-matrix identity expresses the
threaded power sum using r-th powers of diagonal entries; it concerns a
power-sum character, not a determinant of an arbitrary polynomial on a
truncated sequence of weights. These are the inspected theorem scopes,
not an algorithmic complexity result imported from the paper.

## Direct arithmetic comparison

Use a different symbol zeta for an auxiliary torsion parameter. The actual
native parameter q=beta^H has both local orders greater than 16H, while
the prefix length m is less than 16H. Consequently q is not a root of
unity of any prescribed order r<=m in either residue field. A theorem
requiring that specialization cannot be applied with q as such a zeta.

An auxiliary root-of-unity algebra is permissible, with its rank and
operations charged. Its Frobenius map acts on its own quantum variables.
No identified map from those variables to the acquired Seifert data has
been supplied that evaluates

    P_m = product_(i=1..m) K(eta^(2i+1))

as one of the threaded power sums. This is the missing construction; it
is not an impossibility statement about all uses of the paper.

For comparison, the ordinary SL3 power-sum polynomial is cheap when its
two scalar inputs u,v are already supplied. If alpha,beta,gamma have
product one and elementary symmetric sums u,v, their power sums satisfy

    p_0=3, p_1=u, p_2=u^2-2v,
    p_n=u*p_(n-1)-v*p_(n-2)+p_(n-3).

The identity follows directly by summing the characteristic equation
for each root. Binary powering of the initialized 3-by-3 companion
matrix computes p_r in O(log r) operations over a commutative ring, with
no inversions. This does not give a fast determinant of K on the native
m-dimensional weight module: the requested scalar is a product of K at
all weights. Supplying u,v that already encode that determinant would
simply move its acquisition into the input.

## A lawful completion that was actually tested

The native odd-order promise offers one useful way to avoid treating
every added root of unity as a false collision. For d=2^s, all nontrivial
d-th-root rotations of an element in the native odd-order subgroup lie
outside that subgroup. Thus their target-minus-clock factors are units.
The exact Graeffe completion in [induced-norm.md](induced-norm.md) computes

    F_d(Y)=product_j(Y-x_j^d)

in soft O(J*s), and F_d(u^d) has the same zero and nonunit predicates as
F(u) at a native u. This is a direct arithmetic proof; it is not an
application of the SL3 theorem with the inadmissible even order d.

That completion retains all m distinct odd-order clock positions.
The explicit even/odd clock merge instead replaces F by F(X)F(qX),
doubling degree while halving length. Its degree-times-length remains
Jm, so the existing block evaluation still costs soft O(J+sqrt(Jm)).
The independently reviewed calculation separates a legal completion
from an unproved speedup.

The constructive open question is an identity that couples different
native clock positions, retains every collision or provides a licensed
factor branch, and acquires its new data in soft O(J+sqrt(m)). The cited
power-sum cancellation, the new safe completion, and the old finite
q-Weyl/boundary observations do not yet supply that identity.
