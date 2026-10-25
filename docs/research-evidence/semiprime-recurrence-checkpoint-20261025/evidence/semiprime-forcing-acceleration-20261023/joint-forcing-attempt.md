# Executed joint companion/block-transform attempt

23 October 2026. Scratch only. This executes a structured modular-composition
proposal for the initialized bordered recurrence. It returns ALL requested
coordinates, but does not improve the inherited soft(sqrt(JL)) query bound.
It is not a rank obstruction, a new backend, or a factoring advance.

## Exact input and requested vector

Write P_L(T;q)=product_(i<L)(1-q^i T)=sum c_i T^i. Let
D(T)=1+d_1 T+...+d_J T^J and let A be its companion with first row
(-d_1,...,-d_J), subdiagonal1, and b=e_1. The initialized state needed is

    v=sum_(i=0)^L c_i A^(L-i)b.                    (1)

This is the whole vector (a_L,...,a_(L-J+1)), where a_n=[T^n]P_L/D.
The native setup supplies every 1-q^k, 1<=k<=L, as a unit. All scalar
q-binomial block-transform preprocessing and its transpose are therefore
legal; no collision-bearing quantity is inverted.

The characteristic polynomial is

    f(X)=X^J+d_1 X^(J-1)+...+d_J.

Put E=R[X]/f, x=X mod f, R=Z/N. The map p(x)->p(A)b and its inverse are
paid triangular-Toeplitz/Krylov conversions in soft J operations. We use
this map for the FINAL vector conversion, rather than form any dense A.

## Execute the block transpose over the companion algebra

Reversal avoids an unnecessary inverse in E. Set qbar=q^(-1) and

    h=(-1)^L q^(L(L-1)/2),
    P_L^rev(X)=X^L P_L(1/X;q)=h P_L(X;qbar).       (2)

Both h and qbar are acquired units. The unit hypotheses for qbar are
exactly those for q. If P_L(X;qbar)=sum chat_k X^k, the polynomial in
(1) is therefore h*sum chat_k X^k.

Choose B>=1, K=floor((L+1)/B), and ell=L+1-BK<B. For the COMPLETE blocks
define the ALREADY PAID base-ring operator

    C_(n,s)=chat_(Bn+s), 0<=n<K, 0<=s<B.

It is a formally linear circuit with base-ring constants, including
the precomputed unit inverses. Consequently it can be evaluated over E:
apply C^transpose to

    w_n=(x^B)^n.

Its B outputs are exactly

    H_s=sum_(n<K) chat_(Bn+s) (x^B)^n.             (3)

Acquire the ell ragged coefficients by the selected-coefficient batch,
and compute

    z=h*(sum_(s<B) x^s H_s
          + x^(BK) sum_(s<ell) chat_(BK+s)x^s) in E. (4)

Apply the Krylov conversion to z. Equations (2)--(4) prove that the
result is exactly (1), including all J coordinates and the terminal
coefficient. There is no unknown forcing-vector initialization, field
diagonalization, group-order input, or unstated high-degree remainder
supplied to this particular algorithm.

## Full cost of this proposal

Cache the scalar block-transform preprocessing ONCE over R. Its cost is
soft(sqrt L+B+K), including selected coefficients, powers, denominators,
and the ragged batch. Do not charge this startup J separate times.

Generate the K weights w_n in E, for example by repeated multiplication
by x^B. This costs soft(JK+J log(B+1)) base-ring operations. Execute the
linear block circuit over E using monic modular products: each E
addition/product has soft J base-ring cost, hence its transform costs
soft(J(B+K)). The final sum in (4), powers and Krylov conversion fit the
same bound. Thus the concrete dense-quotient implementation costs

    soft(sqrt L + J(B+K) + J),                    (5)

with polynomial-size input exponents included in soft notation. Direct
storage is soft(sqrt L+J(B+K)+J) residues; no claim that all E-valued
intermediates have scalar size is made. Ring-operation bounds become
bit bounds by multiplying by soft(log N). J=0 is the empty vector;
L=0 gives b directly. The displayed construction is for J,L>=1.

Taking B about sqrt L minimizes this implementation at soft(J sqrt L).
At J~r,L~r^2 it costs soft(r^2), whereas the inherited explicit baby-step
query already costs soft(r^1.5). Therefore this proposal is not the next
algorithm to use in the controller.

## What the Frobenius/trace reordering actually leaves

The native f is split with unit-separated roots, so one may equally use
its evaluation basis or trace duality. That changes coordinates of (3),
not its computed scalar. Applying trace or power projection AFTER (3)
uses already computed E-valued outputs. Transposing the base-ring block
circuit lawfully changes C to C^transpose, as used here; it does not
turn an E-valued application into one base-ring application.

The precise joint contraction still to accelerate is

    sum_(s<B) x^s * [C^transpose ((x^B)^n)_(n<K)]_s in E. (6)

The outer multiplication by x^s is important: computing the B quotient
elements separately is sufficient but not demanded by the output.
Thus (5) is only the cost of the executed algorithm, not a lower bound
for (6). A successful new contraction can bypass those intermediates.
The scalar coefficient circuit and the constant-companion Krylov actions
are individually fast; this pass did not find an algebraic combination
that contracts (6) at soft(J+sqrt L), or even beats soft(sqrt(JL)).

The bordered block merge and its rank-one high-order variant remain
valid starting points. In particular the terminal zero scalar does not
cancel the preceding vector, and no short-polynomial/rank-one invariant
is claimed for the growing forcing polynomial. This bounded attempt
establishes no new coverage condition, no restriction oracle, and no
algorithmic impossibility for the original guaranteed native query.

## Inspected source pins

* Initialized bordered recurrence: `/tmp/semiprime-one-shot-construction-20261023/bordered-state-attempt.md`,
  SHA256 `f6f46e27aee4386e6f1b1ae1087d669fa3bfd7fb74dc213f457bdeaa592d337f`.
* Paid scalar C/C^transpose, rational-Newton construction, and one-binomial
  quotient: `docs/research-evidence/semiprime-block-query-20261016/reports/block-transform.md`,
  SHA256 `825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70`.
* Already-paid mixed-matrix actions and distinction from joint extraction:
  `docs/research-evidence/semiprime-block-query-20261016/reports/fast-mixed-matrix-interface.md`,
  SHA256 `4959b0f33989570507b15eb82e8b93c2020449032ad1612b4d4e92b74f1d5767`.

No new external theorem is invoked. No tests, finite examples, source
downloads, tracked edits, or full-family speed claim were made.
