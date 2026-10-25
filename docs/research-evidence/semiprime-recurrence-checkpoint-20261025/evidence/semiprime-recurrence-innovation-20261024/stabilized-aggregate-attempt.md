# Stabilized aggregate attempt: a fast projective prefix that loses the pole

23 October 2026. Scratch only. **No faster covered aggregate is obtained.**
This note actually initializes a constant-precision projective q-sum prefix
in soft m, then proves that its proposed evaluation returns the WRONG zero
bit on the covered source. It also checks a coefficient-content normalizer
and a deterministic restriction schedule at their actual costs. These are
focused failed implementations, not a general lower bound or another
supplied-target reformulation.

## 1. Input retained without free inverses

Use the stabilized native input from
`/tmp/semiprime-residue-construction-20261023/direct-residue-constructor.md`,
SHA256 `fef14acf2ece2918de5561dd1d37a9c39982ecb97ae658b8d1149210841e42b3`.
The charged N-power/order screen either factors or certifies that raising
to N preserves both original beta-subgroup orders and every original hit.
It then acquires q1 and the unit-separated Z_j modulo N^2, and

    F1(X)=product_(j=1)^J(X-Z_j).

The cost is soft m once; it is not recharged at every restriction. Work in
S=Z/N^2Z. For a public interval [a,a+h) inside the original native range,
the acquired lift gives

    d_i=F1(q1^(a+i)-N),
    v_p(d_i)=1 at a local hit and 0 otherwise,   p=P,Q.

There are at most J local hits. The integral rational expression

    R(X)=-N F1'(X-N)/F1(X-N)                            (1)

therefore satisfies, COMPONENTWISE in the p-adic integer rings,

    rho = sum_(i<h) R(q1^(a+i)) mod N.                 (2)

The local p-adic interpretation is a proof object. It is not ordinary
modular evaluation through an invertible denominator in S. In particular
F1(q1^(a+i)-N) is a nonunit exactly at the unknown original hits.

## 2. A completely initialized soft-m projective-prefix algorithm

Set A(X)=F1(X-N) and B(X)=-N F1'(X-N). Modulo N^2 these polynomials
are cheaply acquired by

    A(X)=F1(X)-N F1'(X),     B(X)=-N F1'(X).

This uses polynomial Taylor expansion with integer coefficients, not a
division by factorials. Since every Z_j is a unit,

    A(0) mod N = F1(0) mod N

is a certified unit. Thus the formal X-adic quotient B/A IS legally
available near X=0. Choose k<=J+1 and compute

    r(X)=B(X) A(X)^(-1) mod X^k = sum_(n<k) r_n X^n.

The inverse is computed by ordinary truncated power-series inversion,
starting from the acquired unit A(0). Its cost is soft(J+k); no nonunit
leaf or hidden CRT idempotent is inverted. Next acquire q1^h by binary
powering. For n=1,...,k-1 construct

    G_n(h)=(1-q1^(hn))/(1-q1^n),     G_0(h)=h.

Every displayed denominator is a certified unit, since its index is at
most J and the local q1 orders exceed 16m^2. Numerators are never
inverted. Generate the two short geometric sequences and batch-invert
the denominators, costing soft k. The acquired polynomial

    Z_(h,k)(X)=sum_(n<k) r_n G_n(h) X^n                 (3)

is EXACTLY the truncated formal series

    sum_(i<h) R(q1^i X) mod X^k.

This operation costs soft(J+k+log(h+1)) ring operations with only constant
precision, hence soft m bits at k~J~m. Its entire initialization and
division ledger are explicit. In particular, it computes a real shared
truncated q-sum, rather than accepting the long coefficients as input.

The proposed cheap count was to evaluate (3) at x=q1^a and reduce modulo
N. This precise algorithm fails, for the following exact reason.

## 3. Exact failure: all computed coefficients vanish modulo N

B(X) is divisible by N coefficientwise. A(0) is a unit, so its formal
inverse has coefficients in S. Consequently every r_n, and therefore
every coefficient of Z_(h,k), is divisible by N in S. Thus

    Z_(h,k)(q1^a)=0 mod N                              (4)

for EVERY input and every truncation length k in the algorithm.
But on the original covered rectangle, rho in (2) is nonzero. The output
(4) is therefore the wrong zero-support answer on every such continuing
input. This is a symbolic proof of failure, with no numerical examples.

There is no contradiction with the integral indicator (1). Formula (3)
is a quotient in the NILPOTENT X-adic chart around zero, where A(0) is a
unit. The argument q1^a is a unit, not nilpotent. Evaluation at that argument
does not descend from S[X]/(X^k): it would send X^k=0 to the nonzero unit
(q1^a)^k. A discarded tail cannot be set to zero at this argument.

At a hit, the actual p-adic evaluation in (1) cancels the numerator's
factor N against a denominator with valuation one and can be one modulo
p. The legitimate formal inverse at X=0 has not performed that
specialized cancellation. No such cancellation may be assumed when
evaluating the finite series. Dividing the coefficient prefix by N before
evaluation changes the expression and supplies no identity for rho.

Centering an X-adic chart at q1^a instead would require the block's
constant value at q1^a as initialization. That is the original unacquired
evaluation, not a cheap transport of (3).

## 4. Why coefficientwise block normalization does not help this engine

Another literal proposal is to build a block polynomial and strip any
common factor N from its coefficients, retaining only a projective unit
part and a valuation counter. The actual block is

    D_s(X)=product_(r<s) F1(q1^r X-N).

For every s,

    D_s(0)=F1(-N)^s

is a unit. Its coefficientwise N-content is always zero, including on
inputs with the guaranteed native collision. The diagonal of the acquired
upper-triangular product/derivative matrix has this same unit constant
coefficient. Thus this SPECIFIC pre-evaluation content normalizer never
has permission to divide that matrix or polynomial by N.

It may legally normalize the polynomial by its inverse as a formal series;
that is exactly the initialized projective prefix (3), whose failure at
the unit argument was proved above. Incidental factors from other acquired
coefficients would be valid, but no theorem forces one. The claim here
concerns the proposed coefficient-content normalization, not every
possible projective or p-adic aggregate algorithm.

If instead one acquires an actual block value D_s(q1^a), its gcd and
possible N-division are legal and useful. Those numerical block values
are the acquisition that the formal content operation did not perform.

## 5. Early termination and the actual whole-family schedule

For numerical block values the existing initialized matrix/scalar
baby/giant construction costs

    C(J,h)=soft(J+sqrt(Jh))

at any constant precision. Exact hit valuations may expose a proper
factor when a block has one local hit on one side and several on the
other, after an acquired N-division. That can stop some executions early.
It does not lower the cost already paid to acquire that block.

The promised top rectangle need not be queried: start with its known
nonempty support and query one child. A unit child product selects the
other child; a nonunit selects that child or already returns a factor.
Repeat with public row or seed halves. Saturated leaves retain the
original native recovery. All values are acquired modulo N or N^2;
neither full counts nor growing precision are needed for this search.

Using the actual available C bound, the geometric part of this schedule
is bounded by

    sum_(r>=1) sqrt(Jh/2^r)=O(sqrt(Jh)),

and its input terms cost soft J. Skipping the top query saves a constant,
not an exponent in this ledger. Separate calls on a partition into h/g
short intervals have the charged bound

    soft((h/g)*(J+sqrt(Jg))).

Sharing their preprocessing improves that calculation: acquire the ONE
block polynomial D_g of degree Jg and evaluate it at all h/g public
geometric block starts. This is a valid monic MPE computation at cost

    soft(Jg+h/g+J),

again optimized at soft(J+sqrt(Jh)). The stabilized valuations allow
lawful postprocessing and possible early termination of those acquired
block values. No faster support-preserving replacement for their shared
acquisition has been constructed here.

The hit cap <=J bounds how many intervals can be nonempty, but does not
identify which of the many empty intervals may be skipped. No new
coverage-dependent bound on the first successful public interval is
proved. These are charges of these concrete implementations, not lower
bounds for the actual native source or for arbitrary implicit algorithms.

## 6. Stopping point

This pass supplies an actual constant-precision soft-m calculation (3)
and an exact proof that its suggested unit-argument count evaluation
fails. It also closes the literal coefficient-content normalization and
shows the legal deterministic restriction implementation at its existing
clock. It does not provide an aggregate faster than soft sqrt(Jh), and
does not claim that exact counts or precision J are necessary for all
factor queries.

The unresolved operation remains the specialized, factor-sensitive
evaluation of the projective sum at a unit argument, with pole
cancellations accounted for. The acquired formal inverse at zero,
constant-precision input and bounded hit count do not initialize it in
the tested construction. No new target-only formula is counted as
algorithmic progress, and no new factoring exponent is claimed.
