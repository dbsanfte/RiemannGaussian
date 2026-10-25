# Whole nonlinear twist palettes, 22 October 2026

This continuation acquires an entire public palette of nonlinear twists and
its unit correction factors in soft O(J+sqrt(L)+nu), including bit costs in
the native polynomial-size regime. It does **not** acquire a collision
locator or improve the guaranteed factoring exponent. The proof concerns
every input satisfying the prepared-subgroup contract, rather than a new
selected class of semiprimes.

The [palette proof](reports/nonlinear-quartic-palette.md) and
[independent review](reports/independent-review.md) give the full algebra
and cost ledger. They build on the
[previous Cayley/character packet](../semiprime-twist-character-20261022/README.md).
All assertions here are paper mathematics; no new Lean theorem or complete
factoring implementation is included.

## What is acquired

Work modulo N=PQ, with distinct odd primes. Let x_j,u,q belong to the
prepared common scalar subgroup of odd local orders, and let y_i=u*q^i,
0<=i<L. Assume J,L,nu are polynomially bounded in N. Put

    a_k=u*q^k, 0<=k<nu,
    alpha_a(t)=t+a*i,
    W_a(t)=(t+a*i)/(t-a*i).

The Gaussian denominator norms are units: a zero of t^2+a^2 would give
an element of order four in an odd-order scalar subgroup. This applies
in both split and inert Gaussian local algebras. The nonlinear W_a(t)
need not itself have odd order, so its retained lift character can be
nontrivial.

Acquire the complete products

    A_k=product_j(x_j+a_k*i),
    B_k=product_(h<L)(u*q^h+a_k*i).

All A_k come from one degree-J polynomial and monic multipoint evaluation.
B_0 is one scalar Gaussian geometric product, evaluated with sqrt(L)-size
blocks and monic remainder trees. The rest follow from the unit-safe rule

    B_(k+1)=q^L*B_k*(q^(-k-1)+i)/(q^(L-1-k)+i).

Thus all A_k,B_k cost soft O(J+sqrt(L)+nu), without a length-L seed list.
Repeated evaluation nodes are allowed. Exponentiation, inversions, symbol
computations and O(log N)-bit input/output are charged in the proof and
review. For nu=soft O(m), J~m,L~m^2, the total is soft O(m).

The complete unit corrections

    C_k=(-2*a_k*i)^(J*L)/(conj(A_k)^L*conj(B_k)^J)

are acquired within that same budget and satisfy

    product_(j,h)(W_(a_k)(x_j)-W_(a_k)(y_h))
      = C_k * product_(j,h)(x_j-y_h).

This identity also holds when the original product is a nonunit. No
division by that product occurs. Acquiring all C_k leaves the product on
the right, and the useful localization information, uncomputed.

## The full quartic phase, including its sign

Let S_N be the Gaussian quartic Jacobi symbol with full rational
denominator N, extended by zero on Gaussian elements of nonunit norm.
Let tau(w)=S_N(alpha) for a unit lift w=alpha/conj(alpha), and put
j2=Jacobi(2,N). The previous packet proves lift independence and a public
algorithm which computes tau or factors N.

For arbitrary norm-one w,z with unit difference, choose unit lifts
alpha,beta. Then

    w-z=(alpha*conj(beta)-beta*conj(alpha))
          /(conj(alpha)*conj(beta)).

The numerator is i times a rational unit. Rational units have S_N=1,
and S_N(i)=j2. Consequently the full phase is

    S_N(w-z)=j2*tau(w)*tau(z)

on unit differences, with zero on nonunit differences. This proof matters:
the conjugation identity alone determines only the square of the phase.
The independent review identified that ambiguity; the archived palette
proof includes the repair and the explicit zero convention.

For the W palette this becomes

    S_N(W_a(x_j)-W_a(y_h))
      =j2*S_N(x_j+a*i)*S_N(y_h+a*i)*1_unit(x_j-y_h).

The product of all row and column phases is therefore acquired through
A_k and B_k. After those phases are removed, every member retains the
same uncomputed collision mask. In particular, the known existence of
a collision does not identify which restricted child contains it.

Asymmetric W_a,W_b chords have the same separated phase and numerator
2*i*(a*y-b*x). For a=u*q^r,b=u*q^s they give the original seed window
shifted by r-s. The inexpensive boundary evaluations for adjacent windows
do not determine their shared interior. These facts delimit this concrete
family; they are not an impossibility theorem for other coupled twists.

## A precise remaining evaluation target

The parallel structured-matrix investigation gives a useful target with
unit denominators. Here also require L to be smaller than both local
orders of q, as in the native preparation. Define

    R_k=product_(h=1..k) (1+q^h)/(1-q^h), R_0=1,
    w_i=(-1)^i*R_i*R_(L-1-i),
    f(x)=product_(i<L)(x-y_i)/(x+y_i).

Partial fractions give the exact identity, including at original hits,

    f(x)=1-2*sum_(i<L) y_i*w_i/(x+y_i).

Indeed the residue at -y_i is -2*y_i*w_i, the poles are distinct with
unit differences, and both sides tend to 1. Every displayed denominator
is a unit under the order promises. Thus a new algorithm evaluating
these weighted sums at all J native targets in soft O(J+sqrt(L)) would
acquire all original row collision detectors at the desired cost.

Localization adds no new exponent gap after that hypothetical evaluation.
A nonunit row is selected by J gcds. For that one row, the existing scalar
geometric-product algorithm tests interval halves; their sqrt(length)
costs sum to O(sqrt(L)) along one descent. A proper gcd factors N. At a
saturated leaf the original nonzero exponent certificate and inherited
decoder apply. Original integer-trivial handling and the analytic
assumptions of that decoder remain part of the existing contract.

**The simultaneous weighted-sum evaluator is not supplied here.** Selected
weights are already affordable by the inherited selected-prefix primitive;
acquiring all L weights is too expensive. The inspected q-ultraspherical
and terminating hypergeometric identities return the same unpaid
parameter-dependent products. They do not convert J varying targets into
selected indices of one fixed recurrence. This is the remaining task,
not a claimed consequence of the identities.

## Validation and provenance

The independent review checked the identities, split-algebra unit safety,
monic evaluation, boundary recurrence, bit cost, and the separation of
the root collision promise from localization. Its requested proof and
size clarifications are incorporated in the archived final report.

An optional convention check, carried over from the investigation, runs as

```sh
python3 docs/research-evidence/semiprime-twist-palette-20261022/probes/check_palette.py
```

It compares 405 residual symbols and 12 boundary updates with direct
calculations. Its dependency also replays the previous Gaussian controls.
These are algebra checks, not empirical coverage, scaling measurements,
or an implementation of the complete palette algorithm.

The two reports are verbatim final scratch reports. Their old /tmp
references identify historical working files; the previous portable
packet contains the symbol conventions and primary-source pins. Only
the probe's dependency path was changed for portability; see
[archive-provenance.json](archive-provenance.json). The manifest freezes
this packet independently of the previous packet. No old manifest,
formal source, publication metadata, commit or push is changed.
