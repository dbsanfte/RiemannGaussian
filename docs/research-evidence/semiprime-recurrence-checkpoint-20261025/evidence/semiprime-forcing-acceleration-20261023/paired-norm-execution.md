# Executed split-pair norm: exact source, unchanged acquisition cost

23 October 2026. Scratch only. No accelerated original-query algorithm
is obtained. This executes one initialized paired-norm construction and
tests its next length-doubling state. It does not propose an alternative
uncovered family or a rank obstruction.

Normalize the actual original targets by z_j=Y_j^-1 and let
F(X)=product_j(X-z_j). The original product differs from
product_j P_L(z_j;q) only by an acquired unit, where

    P_L(X;q)=product_(i<L)(1-q^i X).

Let A=(Z/N)[X]/F. Its element X is a unit because every z_j is a
unit. Ordinary ring operations in A cost soft J and need only monic
division; no desired cross difference is inverted.

## 1. A legal initialized pair algebra

In A form

    B=A[T]/(T²-(1+q)XT+qX²).                          (1)

The two roots T=X,qX differ by(q-1)X, an acquired unit: q-1 is
certified by the original short-order setup. Thus the map from a+bT
to its two values at X,qX and its inverse are executable in soft J.
The norm is the division-free formula

    Norm_(B/A)(a+bT)=a²+(1+q)Xab+qX²b².                (2)

It remains valid at zero divisors and desired collisions. Starting
from1, the actual child product P_n(T;q²) can be built, and

    Norm_(B/A) P_n(T;q²)
       =P_n(X;q²)P_n(qX;q²)=P_(2n)(X;q).              (3)

For odd length2n+1 multiply by the known factor1-q^(2n)X.
Every leaf is still an original seed index2i or2i+1; a selected
collision retains the original bounded-leaf decoder. No new
annihilator or source-coverage promise is needed.

Cross-overlaps between virtual targets from different rows may occur.
They do not invalidate(1), which is a split algebra over A, or monic
evaluation at the two explicit target lists. No assertion identifying
that split algebra with a squarefree single polynomial quotient in T
is needed, and no inverse of those cross-overlaps is used.

## 2. What is actually spent

One multiplication by1-q^(2i)T has constant many operations in A.
Thus direct construction is soft Jn. Applying the existing blocked
evaluator instead to the2J explicit virtual targets and length n costs

    soft(2J+sqrt(2Jn))=soft(J+sqrt(JL)).

All q²-factorial units are legal: q has odd local orders, so squaring
preserves those orders, and the indices are within the original
certified horizon. Output norms cost only soft J after the child data
are acquired. The norm itself is not the missing expensive operation.

Further recursive splitting gives2^k J virtual evaluations of length
approximately L/2^k, retaining the same size product JL in this
explicit evaluator. If pushed to rank of order J*sqrt L, the algebra
state is already too large. This is the cost ledger of this executed
implementation, not a lower bound on an implicit norm-only algorithm.

Could one retain only the J parent norm values? That is legal as
storage, but the next length doubling still needs

    P_(4n)(X;q)
       =P_(2n)(X;q)P_(2n)(q^(2n)X;q).

The stored remainder of P_(2n) does not determine its shifted
remainder by naive substitution. If P_(2n)=QF+R, the exact second
factor is

    R(q^(2n)X)+Q(q^(2n)X)F(q^(2n)X) mod F.             (4)

The pair norm has not acquired or cancelled the second term. Calling
the norm descriptor a J-state recurrence would leave this source
initialization/update unpaid.

## 3. Sign/Graeffe and trace folds kept distinct

The other easy quadratic norm is

    P_L(T;q)P_L(-T;q)=P_L(T²;q²).                     (5)

With T²=X it retains length L. For an acquired odd-order root T,
the plus factors1+q^i T are units, so it safely preserves zero support;
it does not compute the different pair X,qX in(3) or shorten length.
Selecting an even/odd SUM coordinate is likewise not this product norm.

One can reindex square-root targets to keep the same q while halving
length, but the two branches remain. Only a proved integer-index
congruence can discard one. The inherited native parity/fourfold and
inversion-trace reductions supply constant gains; they are not new
results here. Repeating them requires additional higher-digit or
changing-carrier information, not just oddness of the group orders.

The inversion fold pairs q^i with q^(2n-1-i), replacing a target Y by
Y+q^(2n-1)/Y and seeds by the matching traces. This is an inherited
exact identity. Its next reflection changes the carrier: two distinct
underlying maps Y->c/Y and Y->d/Y compose to scaling by c/d. A
constant-size descending trace update is not supplied by the first
identity. No composable new trace-seed evaluator was found here.

## Outcome

The split-pair norm avoids an illegal quotient substitution and is
fully initialized from P_0=1. But its present acceleration costs the
same soft(J+sqrt(JL)) as the original blocked query; dropping the
virtual child states reintroduces the precise wrap in(4). A new
constructor that computes the relative norm without acquiring the
child values, or evaluates that wrap jointly, remains necessary for
this approach. No such operation is claimed.

Read scope: original uniform setup/query interface, final
`4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`;
the preceding exact BM/quotient notes; the AGENTS native fold/inversion
duplicate guards identified by root. All finite identities and costs
above are derived over the actual composite ring. No tracked/frozen
edits, numerical examples, downloaded-code execution, backend or new
factoring rate.
