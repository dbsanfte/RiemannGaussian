# Long collision query: literature and arithmetic audit, 2026-10-15

Three parallel GPT-6.1 Sol investigations and a root investigation searched
for a cheaper acquisition of the full collision query. No improvement over
the existing soft O(m^(3/2)) general evaluator was proved. We did identify a
sharper composite-ring modular-composition theorem and prove specific
obstructions to proposed scalar compression routes. These are classical
arguments and literature checks, not new Lean results or a claim of an
arbitrary scalar lower bound.

## Exact acquisition target and existing bound

Over R=Z/N, with known units q,u,Y_j, set

    H(X) = product_(j<=J)(X-Y_j),
    G_L(X) = product_(0<=i<L)(X-u q^i),
    S = product_(0<=i<L) H(u q^i)
      = Res(G_L,H) = (-1)^(JL) Res(H,G_L).

We need the long query at J=soft O(m), L=Theta(m^2), including its original
variable origins and lengths, in soft O(m) bit time and controlled memory.
H itself is already cheaply available. Constructing G_L modulo H would be
a sufficient intermediate if its cost and subsequent factor-aware resultant
cost were paid; computing the scalar or its gcd directly could be weaker.
No step may invert a possible collision residual.

The verified generic construction costs

    soft O((J+sqrt(JL)) (log N+log(JL))) bits.

It builds blocks of degree Jb, evaluates L/b blocks, and balances these at
b~sqrt(L/J). Chirp evaluation and Kronecker multiplication work over the
composite ring using only the supplied unit q. Rescaling targets and
disjoint binary decompositions handle the actual origins and ragged lengths
without padding. See [the preserved baseline](baselines/q-factorial-upper-bound.md)
and [the fresh degree-sensitive audit](reports/q-product-literature.md).

The fresh Bostan–Yurkevich check confirms that its multiple-index results
concern one recurrence and retain growing coefficient degree. Distinct
target parameters cannot be treated as free indices of that recurrence.
The Nogneng–Schost lead concerns quadratic-exponent sums, with different
one-point and arbitrary-point costs; it supplies no missing q-Pochhammer
batch theorem. See [the focused primary check](reports/nogneng-schost-check.md).

## A sharper available modular-composition primitive

Van der Hoeven–Lecerf, *Fast modular composition using spiroids*, Theorem 1,
gives deterministic explicit degree-D modular composition over arbitrary
Z/N in

    D^(5/sqrt(log D)) * soft O(D log N)

bit operations. The author manuscript is dated August 12, 2026; publisher
metadata gives October 2026 publication. The theorem's ring hypothesis and
square root in the exponent were checked directly on page 1 of the PDF.
[Primary paper](https://www.texmacs.org/joris/fftcomp/fftcomp.pdf).

Kedlaya–Umans already allowed composite coefficient rings. The new result
improves the explicit subpolynomial overhead; composite-ring applicability
is not itself a new invention in 2026. This removes any reason to reject
composition merely because N is unfactored, but supplies no implicit-product
remainder algorithm. Its input consists of explicit degree-bounded arrays.

The factor D^(5/sqrt(log D)) is superpolylogarithmic. Thus this is an
almost-linear D^(1+o(1)) bound, not strict soft O(D). Even a successful
reduction using this bound alone would still need that overhead accounted
for against the requested strict soft O(m) target. See
[the detailed source and interface audit](reports/implicit-norm-literature.md).

## Actual-family obstruction to reusing one remainder

Geometric doubling is exact:

    G_(2h)(X) = G_h(X) q^(h^2) G_h(q^(-h) X).

However, knowing G_h modulo H does not give the second factor modulo H.
For an arbitrary polynomial V, the proposed operation [V(X)] -> [V(cX)]
on R[X]/H is well defined exactly when H divides H(cX). Comparing V=0
and V=H proves necessity. Substituting into a multiple of H proves
sufficiency.

This failure is forced on the existing prime-order hard family, rather
than being merely a generic-target concern. Reduce to either hidden field,
where q has prime order R_p>J and H(0) is nonzero. If H divides H(q^s X),
both polynomials have degree J and leading coefficients 1 and q^(sJ), so

    H(q^s X) = q^(sJ) H(X).

Comparing constant coefficients gives q^(sJ)=1, hence R_p divides sJ.
For 0<s<R_p and 0<J<R_p this is impossible. The retained family has
R_p>m^2.031 up to fixed constants, whereas the relevant nonzero doubling
shifts are O(m^2), and J=soft O(m). Thus all such shifts eventually fall
in the excluded range. Negative shifts satisfy the same argument.

A valid moving-carrier algorithm instead acquires G_h modulo the monic
polynomial q^(-hJ) H(q^h X). No impossibility of acquiring that data
implicitly is asserted. A literal product over shifted normalized source
nodes has degree equal to its number of listed factors; global distinctness
modulo N alone does NOT prove a minimum vanishing-polynomial degree over
this composite ring. See [the source-specific analysis](reports/moving-carrier.md).

## Cheap series truncation loses exactly the needed information

For H(0) a unit, x=[X] is a unit in A=R[X]/H. Consequently x^K A=A for
every K. For any prescribed K-jet T and any desired residue a in A,
choose B representing x^(-K)(a-T(x)). The polynomial T+X^K B has that
jet and residue a. Identical jets can therefore have norms 0 and 1.

The low coefficients of a q-product CAN be acquired cheaply, even without
logarithms: geometric doubling modulo X^K costs soft O(K log L), since
(X^K) is stable under scaling. There is no general jet-to-H-remainder or
jet-to-norm map. Reciprocal truncation has the same issue for unit roots.
This does not exclude an algorithm exploiting the additional specific
q-product description. See [the full proof](reports/formal-log-obstruction.md).

Ordinary rational multiplicative telescoping also fails: if a positive
degree F with nonzero constant term were c X^a V(qX)/V(X), its valuation
at zero would force a=0, while its valuation at infinity would then have
to be both -deg F and zero. This rules out that rational endpoint form,
not length-dependent special functions or richer scalar circuits.

## A gcd-only shortcut has a concrete bit-cost obstruction

On the prime-local-order squarefree family, replacing residual powers
gamma^k-1 by gamma^K-1, with K the exact LCM of the nonzero |k|, preserves
the gcd with N. This avoids materializing the residual matrix algebraically.

For the actual first-current long rows it does not achieve the clock.
The source identities give, for a common gamma-power origin gamma^v,

    j^2 (E_j-v-m^2 i) = N(j-1)^2-v j^2 (mod m).

At most two tags have these exponents divisible by m. Every other long row
contains a signed primitive arithmetic progression of step m^2. The
elementary bound

    lcm(a,a+d,...,a+(n-1)d) >= a d^(n-1),  gcd(a,d)=1,

applied to at least half the terms proves that the exact LCM requires
Omega(L log m)=Omega(m^2 log m) bits. Any nonzero common multiple has the
same size obstruction. Formal exponentiation producing that exact integer
exponent also needs at least its logarithm in addition/subtraction-chain
operations. Neither claim applies to algorithms using an independently
proved order reduction or other modular arithmetic tricks.

See [the complete source-specific proof](lcm-exponent-obstruction.md), which
received two independent algebraic reviews. This is an acquisition
obstruction to a concrete gcd-only route, not an assertion that all gcd-only
queries are expensive.

## What remains worth attacking

A sufficient new theorem would compute G_L modulo H, or directly its scalar
resultant, in soft O((J+sqrt L) polylog N) for these supplied parameters and
their ragged analogue. At J~m,L~m^2 this meets the desired acquisition rate.
Demanding soft O(J polylog L) for every J would be unnecessarily stronger:
it would also demand a polylogarithmic scalar q-factorial algorithm at J=1.
The balanced regime alone is the present target.

Equivalently, for a rectangular normalized collection, put

    B(t)=product_j(1-a_j t),
    T(t)=product_j product_(i<L)(1-a_j t q^i).

Then B(t)T(qt)=B(q^L t)T(t), T(0)=1, and the query is T(1).
The equation has small coefficient degree J, while T has degree JL.
Evaluating the specified product solution cheaply would be a substantive
advance. In finite order, the equation and constant term do not in general
uniquely identify a solution: invariant rational functions of t^ord(q)
must be controlled. Formal-series solutions and generic composition do
not by themselves supply evaluation at t=1.

There is a valid easy branch when a public period t with q^t=1 is supplied
and t=soft O(m): evaluate one period and the remaining prefix, then take
the integer power of the full-period product without division. This costs
soft O(J+t+log L) ring operations. It does not handle the retained large-
order family. No new collision coverage or proper-factor recovery follows
from the research in this bundle. The deterministic all-semiprime
one-sixth goal, its total bit/memory proof and Lean completion remain open.

## Evidence and review status

`manifest.json` records repository HEAD, exact report and primary-source
hashes, historical baseline provenance and source URLs. Primary PDFs are
stored as lossless gzip copies; their manifest hashes cover both compressed
bytes and original PDF bytes. Reports preserve the investigators' original
text, including their original temporary paths; the manifest maps those
paths to durable bundle files. Older frozen audits were not rewritten.

The literature claims were checked against primary text; the scalar
algebra received independent Sol 6.1 reviews. The source's inherited
large-order supply and interval-count theorems were used as recorded
historical inputs, not re-proved in this session. No new Lean source,
certificate corpus, build, factorization experiment or exponent improvement
is claimed.
