# Exact scalar q-factorials over the semiprime ring

2026-10-08. Classical analysis only; no native changes or claimed 1/6 algorithm.
The actual antipodal and inverse-indexed candidate notes are retained unchanged.

## Primary algorithm and the composite-ring transfer

Bostan–Yurkevich Algorithm 3 and Section 3.4 balance block degree against the
number of geometric evaluation points. Their Theorem 5 keeps the polynomial
coefficient degree in the complexity. The author-hosted April 14, 2022 text
was freshly inspected; it is a different PDF from the preserved 2020 arXiv v1,
with the same relevant degree-sensitive construction. [Primary paper](https://yurkevi.ch/data/Alin%20Bostan,%20Sergey%20Yurkevich_2020_Fast%20Computation%20of%20the%20N-th%20Term%20of%20a%20q-Holonomic%20Sequence%20and%20Applications.pdf).

The following is a direct ring-valid specialization and bit-cost derivation.
Let R=Z/NZ, b=ceil(log2(N+1)), q a supplied unit, and
F(X)=prod_(j=1)^J(z_j-X), with supplied z_j in R. Define

    U_L = prod_(i=0)^(L-1) F(q^i).

For J,L>=1 choose s=max(1,ceil(sqrt(L/J))), T=floor(L/s), r=L-sT.
Construct P_s(X)=prod_(i<s)F(q^i X) by repeated geometric doubling:

    P_(2t)(X)=P_t(q^t X) P_t(X),
    P_(2t+1)(X)=F(q^(2t)X) P_t(q^t X) P_t(X).

Then exactly, without cancellation,

    U_L = prod_(k<T) P_s(q^(sk)) * prod_(i<r) F(q^(sT+i)).

All large geometric evaluations can be performed by one chirp convolution.
For P(X)=sum_(k=0)^D c_k X^k and Q a unit, put

    A_(D-k)=c_k Q^(-binom(k,2)), B_h=Q^(binom(h,2)).

If C=A*B, then P(Q^i)=Q^(-binom(i,2)) C_(D+i). This follows from
binom(i+k,2)=binom(i,2)+binom(k,2)+ik. For T desired evaluations,
only h<=D+T-1 is needed. The binomial exponents are ordinary integers;
no division by 2 in R is used. The only inversion is the known unit Q.
The tail uses the same identity with shifted coefficients of F.
Products, evaluations and zero residuals are valid over any commutative ring.
Neither F(q^i) nor an intermediate norm is ever inverted.

Canonical coefficients below N permit integer Kronecker multiplication:
choose a binary digit width larger than 2b+ceil(log2(D+1)), multiply the
packed integers, unpack, and reduce the coefficients modulo N. Consequently
a polynomial multiplication of length D costs soft O(D(b+log(D+1))) bits,
using fast integer multiplication. This elementary encoding needs no roots
of unity or field divisions. The standard multitape bound is supported by
[Harvey–van der Hoeven, Theorem 1.1](https://www.texmacs.org/joris/nlogn/nlogn.pdf).

Building F costs soft O(Jb). The block construction and evaluations cost
soft O((Js+T+J+r)b), where logarithms of these dimensions are hidden.
Since s<=1+sqrt(L/J), this proves the exact scalar upper bound

    soft O((J+sqrt(LJ))b)

including its fixed-width residue operations. Computing public unit powers
from polynomial-bit-size integer exponents adds soft O(Jb), and one public
extended gcd supplies q^(-1) with polylogarithmic overhead. If a supplied
normalizer is not known to be a unit, its gcd must be checked first; a proper
gcd returns a factor, while gcd=N does not license inversion.

## Variable origins and lengths retain the same upper bound

For public units x_j,u_j and nonnegative lengths L_j<=Lmax, the product
prod_j prod_(i<L_j)(x_j-u_j q^i) is the known unit prod_j u_j^L_j
times prod_j prod_(i<L_j)(x_j/u_j-q^i). Thus pair-dependent baby origins
are absorbed into the public targets without an oracle. Known signed starts
are absorbed by an additional unit power of q.

No full-interval padding is required. For each set bit k of L_j, set
o_(j,k)=floor(L_j/2^(k+1))*2^(k+1). Its disjoint block is
[o_(j,k),o_(j,k)+2^k). Shift that target by q^(-o_(j,k)), retain the unit
phase q^(o_(j,k)*2^k), and group equal block lengths. If J_k targets occur
in group k, its scalar cost is soft O((J_k+sqrt(2^k J_k))b).
Because J_k<=J and sum_k 2^(k/2)=O(sqrt(Lmax)), the total is

    soft O((J+sqrt(J Lmax))b).

This handles unequal original row lengths and both reciprocal target legs;
the original units and endpoints remain exact. It also gives the composite-
safe interpretation of the antipodal trace product: use its two known
original targets, rather than introduce a square-root oracle for the trace.

For the actual publicly acquired row packets J=soft O(m), Lmax=O(m^2),
the bound is soft O(m^(3/2)). It avoids degree J*Lmax expansion but does
not pay the required soft O(m) whole-family acquisition budget.

## Precise bottleneck for this evaluator

With a common long interval and a unit leading coefficient, deg P_s=Js
exactly over R. This literal dense-block evaluator writes Js+1 coefficients
and T=floor(L/s) evaluated block values. For 1<=s<=L,
Js+T>=Js+L/s-1>=2sqrt(JL)-1. Thus its explicit acquisition contract has
an Omega(sqrt(JL)) residue-word floor, for every choice of blocking parameter.
At J=Omega(m), L=Omega(m^2), this contract cannot deliver soft O(m).
The floor is for the specified coefficient-and-evaluation backend, not a
lower bound on implicit circuits, other scalar algorithms, or factoring.

The full public Hensel relation r_j^2=4Na_j mod m^2 is useful additional
structure, but supplies no identity expressing these literal P_s blocks or
their collective product with soft O(m) circuit cost. Bostan et al.'s
*Fast Computation of Special Resultants*, Theorem 1, computes composed
polynomials with their full product degree retained; it supplies no missing
scalar query theorem for these phase-dependent parameters. [Primary paper](https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf).

No guaranteed nonunit value, factor coverage, proper recovery, new recurrence
compression, or formal bit-clock theorem is inferred from this scalar upper
bound. The positive soft-O(m) implicit-query gate remains open.

