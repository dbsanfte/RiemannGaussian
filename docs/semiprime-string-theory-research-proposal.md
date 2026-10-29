# String-theory identities for the semiprime collision query

Date: 26 October 2026

Status: research proposal; no improved acquisition bound is established

## Objective

Investigate whether identities from topological strings and supersymmetric
gauge theory can reduce the cost of acquiring the complete arithmetic
collision query used by the semiprime factorization project.

The primary direction is **Nekrasov boundary cancellation applied to the
coloured row lattices**. Schur-function identities provide an exact expression
against which to check preservation of collision information. The supporting
directions are collective recurrences from `qq`-characters and spectral
duality between lattice directions.

The intended outcome is an algorithm with a uniform proof of coverage,
factor recovery, and whole-family cost. A compact formal expression alone
does not establish that outcome. The guaranteed deterministic classical
factorization target remains \(\widetilde O(N^{1/6})\), with full bit-complexity
accounting and eventual formal verification.

This proposal records the side-conversation literature investigation. It
does not report execution of the proposed work packages or change the
project's established mathematical status.

## 1. Arithmetic problem and baseline

Use the prepared contract and notation of the existing
[stationary-colour construction](research-evidence/semiprime-knot-trace-20261026/README.md)
and [collective colour-query report](research-evidence/semiprime-knot-colourquery-20261026/README.md).
In particular,

\[
N=PQ,\qquad R=\mathbb Z/N\mathbb Z,\qquad
k\asymp N^{1/6},\qquad H=k^2,\qquad q=\beta^H,
\]

where the inherited preparation handles exceptional cases and supplies the
required unit and local-order conditions. Neither prime factor is known.

There are \(J=\widetilde O(k)\) acquired row roots

\[
y_j=\beta^{E_j},\qquad E_j=a_j+b_jN+\lambda_j,
\]

with retained integer labels and source metadata. The complete signed clock
has length \(h=O(k^{3/2})\). The baseline complete query costs

\[
\widetilde O(J+\sqrt{Jh}),
\]

which gives \(\widetilde O(k^{5/4})=\widetilde O(N^{5/24})\) at these parameter
scales. This is the cost of this route, not a claim about the best general
factoring algorithm.

The desired whole-family query bound is

\[
\widetilde O(J+\sqrt h)=\widetilde O(k),
\]

or another bound sufficient to fit the complete algorithm into the same
\(\widetilde O(k)\) budget. Here and below, logarithmic factors must be
accounted for in \(\log N\), not hidden as constant-cost arithmetic.

For a common original clock interval \(L\le i<L+h\), define

\[
x_j=q^L y_j^{-1},\qquad
C(t)=\prod_{j=1}^{J}\prod_{i=0}^{h-1}(1-tx_jq^i).
\tag{1}
\]

Then

\[
\prod_{j=1}^{J}\prod_{i=0}^{h-1}(y_j-q^{L+i})
=\left(\prod_{j=1}^{J}y_j^h\right)C(1).
\tag{2}
\]

The multiplier is a known unit. Thus (1) gives an exact normalized target.
Row-dependent windows require their own explicit treatment; they cannot be
replaced by a common padded window without checking the decoder and cost.

The inherited coverage theorem concerns an actual row-clock collision at a
hidden prime. A proper gcd yields a factor. A saturated original leaf can
invoke the inherited short-annihilator consumer, at its stated cost
\(T_{\mathrm{ext}}=\widetilde O(N^{31/192})\). Arbitrary zeros of newly
introduced observables do not automatically have this decoder. Evaluating
one aggregate scalar also does not automatically provide a cheap method for
locating an original leaf.

## 2. Main candidate: cancellation from boxes to corners

### 2.1 Exact finite identity

For formal variables \(z,u,v\), put

\[
Z_{r,s}(z)=\prod_{a=0}^{r-1}\prod_{b=0}^{s-1}(1-zu^av^b).
\]

Direct cancellation gives

\[
\frac{Z_{r,s}(z)Z_{r,s}(uvz)}
     {Z_{r,s}(uz)Z_{r,s}(vz)}
=
\frac{(1-z)(1-zu^rv^s)}
     {(1-zu^r)(1-zv^s)}.
\tag{3}
\]

The ratio of four products over a rectangle reduces to four corner factors.
For arithmetic specialization, use the cleared polynomial identity

\[
Z_{r,s}(z)Z_{r,s}(uvz)(1-zu^r)(1-zv^s)
=Z_{r,s}(uz)Z_{r,s}(vz)(1-z)(1-zu^rv^s).
\tag{4}
\]

Equation (4) holds over any commutative coefficient ring. Evaluating the
rational expression (3) requires invertible denominators.

For a finite Young diagram \(D\subset\mathbb Z_{\ge0}^2\), define

\[
K_D(u,v)=\sum_{(a,b)\in D}u^av^b,
\qquad
Z_D(z)=\prod_{(a,b)\in D}(1-zu^av^b).
\]

The signed character

\[
S_D(u,v)=1-(1-u)(1-v)K_D(u,v)
\tag{5}
\]

is supported at the addable corners and shifted removable corners. Taking
the corresponding multiplicative factors produces

\[
Y_D(z)=(1-z)\frac{Z_D(uz)Z_D(vz)}{Z_D(z)Z_D(uvz)}.
\tag{6}
\]

This is the finite algebraic mechanism behind the boundary expressions for
Nekrasov's \(Y\)-observables. The relevant source formulas are (127), (128),
and the multiplicative version (198) in [Nekrasov, BPS/CFT correspondence][1].
Equations (3)--(6) here use an explicitly stated finite normalization.

### 2.2 Connection to the native row support

Before imposing colours and phases, the positive row support

\[
D_k=\{(a,b)\in\mathbb Z_{>0}^2:ab<k\}
\]

is a Young diagram after translating its indices by \((-1,-1)\). Its row
lengths are

\[
\ell_a=\left\lfloor\frac{k-1}{a}\right\rfloor.
\tag{7}
\]

There are \(O(\sqrt{k})\) distinct positive lengths: for
\(a\le\sqrt{k-1}\) there are at most \(\sqrt{k-1}\) indices, and for larger
\(a\) the quotient is at most \(\sqrt{k-1}\). Consequently the diagram has
\(O(\sqrt{k})\) staircase corners, despite containing
\(\Theta(k\log k)\) boxes.

This is a structural observation about the uncoloured positive support. It
is not a bound on the boundary complexity of the actual phased family.
Other sign sectors, axes, deletions, and colour incidences must remain in
the accounting.

### 2.3 Incorporating colours and phase carries

For a unit colour \(c\pmod k\), the existing construction supplies

\[
\Lambda_c=\{(a,b):ac^2\equiv bN\pmod k\}.
\]

Choose the prescribed integer representatives for \(c\) and its inverse
\(c^{-1}\pmod H\), and set

\[
\mu_c(a,b)=-ac-bNc^{-1},\qquad
\tau_c(a,b)=\left\lfloor\frac{\mu_c(a,b)}H\right\rfloor,
\qquad
\lambda_c=\mu_c-H\tau_c.
\]

The unwrapped scalar character is

\[
\widetilde y_c(a,b)
=\beta^{(1-c)a+N(1-c^{-1})b},
\qquad
y_c(a,b)=q^{-\tau_c(a,b)}\widetilde y_c(a,b).
\tag{8}
\]

It is multiplicative on the lattice, but recovering the native phase moves
the clock endpoint:

\[
y_c(a,b)-q^i
=q^{-\tau_c(a,b)}
 \bigl(\widetilde y_c(a,b)-q^{i+\tau_c(a,b)}\bigr).
\tag{9}
\]

The exact colour-character and carry formulas are already established in
the [trace-recurrence report](research-evidence/semiprime-knot-trace-20261026/trace-recurrence.md).
They are inputs to this proposal, not new results.

The research task is to determine whether (5)--(6) can operate on a finite
description of these lattice supports with their actual carries and clock
boundaries. A Young diagram in ambient coordinates need not remain a Young
diagram in a colour-lattice basis. Also, independent startup costs for
\(\Theta(k)\) colours can exceed the desired budget even when each individual
colour has a compact description.

### 2.4 Information that cancellation must preserve

An interior collision factor can occur in both numerator and denominator
of (3) or (6), then disappear from the reduced boundary expression.
Therefore a short boundary expression does not by itself detect all
original collisions. Clearing denominators makes an identity valid but
does not make the zero sets of its individual factors equivalent.

Seek one of the following concrete outputs:

- A boundary observable equal to the required collision product times an
  acquired unit, with an efficient decoder.
- A finite collection of boundary observables that collectively detects
  the guaranteed witness and permits factor recovery within the budget.
- A cancellation algorithm that retains sufficient information about
  cancelled nonunits to recover a factor, with the cost of obtaining that
  information included.
- A new sparse boundary family with its own all-semiprime coverage and
  decoding theorem.

The last option can depart from the existing full product. It must replace
its coverage theorem explicitly rather than assume that boundary support
inherits it.

## 3. Exact alternative representation: Schur functions

The dual Cauchy identity rewrites (1) as

\[
C(t)=\sum_{\nu\subseteq(h^J)}
(-t)^{|\nu|}
s_\nu(x_1,\ldots,x_J)
s_{\nu'}(1,q,\ldots,q^{h-1}),
\tag{10}
\]

where \(\nu'\) denotes the transposed partition and \((h^J)\) is the
rectangle with \(J\) rows of length \(h\).

This is a finite identity of polynomials with integer coefficients. It
therefore remains valid over \(R\), including at collisions. No inversion
of a collision factor is required by the identity itself. Its two factors
separate the row alphabet from the geometric clock alphabet.

Appendix A of [Hyun--Yi][2] records the skew-Schur identities used in
topological-vertex calculations. [Bryan--Kool--Young][3] supplies examples
of evaluating topological-vertex traces through vertex-operator
commutation and specializations.

Direct expansion of (10) is unsuitable: the rectangle contains
\(\binom{J+h}{J}\) partitions. The proposed investigation is to find a
symbolic contraction using the actual colour-lattice alphabet, perhaps
through skew-Schur cancellation or a small collection of boundary states.
Any principal-specialization formula involving divisions must be audited
separately over the composite ring.

Equation (10) provides an exact reference expression for candidate
transformations. A proposed simplification should exhibit its relation to
this polynomial, or to an explicitly sufficient factor-detecting
observable, before its size is treated as an algorithmic saving.

## 4. Collective recurrences from qq-characters

In the gauge-theory setting, \(qq\)-characters combine shifted
\(Y\)-observables so that poles cancel after taking a specified weighted
expectation. For example, in Nekrasov's additive \(A_1\) setting,

\[
\mathcal X(x)=\mathcal Y(x+\varepsilon)
  +\mathfrak q\,\frac{\mathcal P(x)}{\mathcal Y(x)},
\tag{11}
\]

has a polynomial expectation under the stated gauge-theory measure.
The coupling \(\mathfrak q\) in (11) is not our arithmetic clock base
\(q\). The polynomiality theorem concerns the expectation; it does not
assert that an arbitrary rational expression of the form (11) is a
polynomial. [Kimura--Pestun][4] develops the corresponding algebraic
pole-cancellation and screening-operator formalism.

The proposed arithmetic analogue is a finite collection of observables
built from native colour and twist states, with a closed recurrence for
the complete query or a sufficient detector. Establishing that analogue
requires explicit answers to four questions:

1. What is the finite arithmetic state set and its acquired weighting?
2. Which exact identity makes the recurrence close, including boundary
   and phase-carry terms?
3. How are its initial values and any coefficients obtained without
   evaluating the original expensive query?
4. What theorem connects its output to an original collision or directly
   to a factor?

A recurrence of small order can still be expensive if its coefficients,
initial data, or long advancement are expensive. All three costs belong
in the proposed bound. A weighted sum of states also needs a proof that
cancellation does not erase the witness the algorithm seeks.

## 5. Supporting direction: spectral duality

Certain cluster-integrable models exchange the number of chain sites and
the dimension of the auxiliary space. [Marshakov--Semenyakin][5] constructs
this correspondence using a rectangular bipartite graph and relates its
parameters to twists and inhomogeneities. [Awata et al.][6] connects
topological-string amplitudes, refined topological vertices, and integrable
transfer operators through the Ding--Iohara--Miki algebra.

For this project, investigate whether an explicit specialization exchanges
the long clock direction with a direction described by the acquired rows.
The specialization must retain the original finite endpoints and all
normalizing factors.

The acceptance criterion is a reduced acquisition cost after constructing
the dual data. A swap of matrix dimensions, a formal Fourier transform,
or a smaller determinant with expensive entries is insufficient. This
direction is lower priority until a concrete finite arithmetic model is
identified.

## 6. Proposed work packages

The packages below are separable investigations for a future research run.
They have not been assigned or executed by writing this proposal.

| Package | Concrete work | Required deliverable |
| --- | --- | --- |
| A: native boundary construction | Apply finite differences to the coloured support while retaining carries, signs, axes, deletions, and original windows. | Explicit boundary factors or states, with a whole-family description and acquisition bound. |
| B: collision-preserving cancellation | Determine what happens to every original collision under the proposed bulk cancellation. | A factor-recovery theorem or a precise scoped failure of the proposed cancellation rule. |
| C: Schur contraction | Specialize (10) to the acquired row alphabet and test finite skew-Schur or vertex-operator reductions. | An exact contracted expression plus the cost of acquiring and evaluating it. |
| D: qq-character recurrence | Identify a finite arithmetic weighting and prove closure of a collective observable. | Initialized recurrence, boundary equations, advancement cost, and decoder. |
| E: spectral-duality specialization | Map the native finite query into a suitable lattice model and acquire its dual data. | Exact parameter map and a complete comparison with the baseline cost. |

Start with A and B together. Use C to check exact preservation of the
collision polynomial when appropriate. Pursue D when an explicit finite
state model emerges; pursue E when a concrete dual parameter map is
available. Formal resemblance alone should not trigger a large
implementation effort.

## 7. Proof obligations and success criteria

### Uniform arithmetic validity

A result must apply to every input under the prepared contract. If it
changes the family, prove coverage for that family across the full
semiprime range. Finite successful examples are diagnostics, not a
replacement for this theorem.

All finite-ring identities must retain their actual unit hypotheses.
Formal or analytic identities from the literature require an explicit
specialization. Infinite products, analytic continuation, and roots of
unity cannot be substituted for the finite high-order arithmetic clock
without proof.

### Complete acquisition and decoding cost

Record the costs of support construction, all colours, phase carries,
coefficient acquisition, initialization, recurrence advancement or
contraction, gcds, localization, and any terminating extraction branch.
Charge all auxiliary extension degrees and all bit lengths.

If decoding uses restricted queries, prove and cost those queries.
Alternatively, supply a decoder that does not require restriction
stability. The inherited extractor must retain its actual cost; a short
integer label does not make that cost polylogarithmic.

### Levels of outcome

- **Representation result:** an exact new identity or acquired boundary
  description. Useful infrastructure, but no improved factoring exponent.
- **Algorithmic advance:** a uniform improvement in the complete query
  bound with a valid decoder. Report its actual dependence on \(J,h,k\)
  and any remaining cost elsewhere in the algorithm.
- **Acquisition target achieved:** the entire relevant query and decoding
  stage fits \(\widetilde O(k)\), uniformly across the family.
- **Full factorization target achieved:** the acquisition result is
  integrated with preparation and recovery, and the complete deterministic
  \(\widetilde O(N^{1/6})\) bit-complexity proof is finished. Formal proof
  status must be reported separately and accurately.

A scoped failure should identify the exact attempted construction and
missing property. Failure of one boundary quotient or duality does not
establish a general impossibility result for these techniques.

## 8. Initial milestone

The first substantive milestone is a finite boundary construction for the
actual coloured family, accompanied by a theorem explaining how original
collisions survive or are recovered during cancellation. It should expose
the total acquisition cost before any new factoring implementation or
formalization campaign.

The central research question is:

> Can the two-dimensional boundary cancellation of the row support be
> combined with its exact colour characters and finite clock boundaries
> so that a guaranteed arithmetic collision remains recoverable in
> softly linear whole-family work?

## References

1. Nikita Nekrasov, *BPS/CFT correspondence: non-perturbative
   Dyson--Schwinger equations and qq-characters*, arXiv:1512.05388.
   [Paper][1]. Relevant passages: equations (127)--(128), the polynomiality
   theorem in section 6.1, equation (148), and equation (198). These concern
   the specified gauge-theory observables; no semiprime specialization is
   supplied by the source.
2. Seungjoon Hyun and Sang-Heon Yi, *Non-compact Topological Branes on
   Conifold*, arXiv:hep-th/0609037. [Paper][2]. Appendix A supplies Schur and
   skew-Schur identities used in topological-vertex computations.
3. Jim Bryan, Martijn Kool, and Benjamin Young, *Trace identities for the
   Topological Vertex*, arXiv:1603.05271. [Paper][3]. Section 5 gives
   vertex-operator trace calculations and commutation identities for its
   stated specializations.
4. Taro Kimura and Vasily Pestun, *Quiver W-algebras*, arXiv:1512.08533.
   [Paper][4]. Sections 4--5 develop pole cancellation and the algebraic
   operator construction.
5. A. Marshakov and M. Semenyakin, *Cluster integrable systems and spin
   chains*, arXiv:1905.09921. [Paper][5]. Provides the rectangular-lattice
   model and spectral duality relevant to the proposed change of direction.
6. Hidetoshi Awata et al., *Toric Calabi--Yau threefolds as quantum
   integrable systems. R-matrix and RTT relations*, arXiv:1608.05351.
   [Paper][6]. Connects refined topological vertices, transfer operators,
   and spectral duality in the stated representations.

[1]: https://arxiv.org/html/1512.05388
[2]: https://arxiv.org/pdf/hep-th/0609037
[3]: https://arxiv.org/html/1603.05271v2
[4]: https://arxiv.org/html/1512.08533
[5]: https://arxiv.org/abs/1905.09921
[6]: https://arxiv.org/abs/1608.05351
