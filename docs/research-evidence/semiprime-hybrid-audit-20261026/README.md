# Which walls are shared, and which gains can be combined?

26 October 2026. Audit of the 24–26 October research record, with three
parallel Sol 6.1 investigations of concrete candidate hybrids.

**Both patterns occur.** We have made different parts of the problem
easier in different representations. But many exact algebraic rewrites
still require the same collision-sensitive finite product, or one of
its selected derivatives. The strongest compositions tested here do
not yet connect a cheap supplier to a sufficient cheap decoder. There
is no new whole-query exponent or guaranteed sixth-exponent algorithm.

The retained route costs soft O(k^(5/4)) for k of order N^(1/6).
This is the bound for this research route, not a best-known general
factoring claim. A complete target result must include acquisition,
all-input coverage, recovery and bit complexity; the final formal
proof also remains open.

The formulas below use the existing prepared branch: N=PQ, k=2*3^e,
H=k^2, q=beta^H, and P,Q>16H. The previously paid preparation handles
the complementary branches. Local order and unit guards are retained.

## What the representations actually improve

| Representation group | Useful part already supplied | Where it stops | Nature of the wall |
|---|---|---|---|
| Signed weighted Gauss rows and the complete scalar phase catalogue | Uniform coverage; O(k) row data and an O(k^(3/2)) clock | Joint readout costs soft O(k^(5/4)) | Acquisition of the collision product |
| Nonsplit torus, adjugate, subresultant and projective gradient | Under the good orientation, a unique hit and a decoder from two outputs or a coarse factor residue | Neither the required outputs nor the unconditional good-orientation palette are supplied at target cost | Readout **and** promise supply |
| q-binomial moments, Hankel/Christoffel and Bethe/TQ cores | Short moments and a small polynomial core are genuinely acquired cheaply | The full norm or its useful first variation is outside that acquired data | Nonlinear readout of cheap linear data |
| Alexander/Seifert, torsion, skein and knot prefix formulations | Exact realization; recovery needs only prefix nonunit bits in the appropriate covered family | No fast algorithm for those bits follows from the small representation | Collision predicate acquisition |
| Cyclic norms and resolvents | Cheap marginal norms and, at small cyclic rank, an initialized inverse action | The correction connecting the auxiliary cycle to the physical finite clock contains the original q-product | Missing correction between two cheap models |
| Common-character lattices, sheared slices and finite multiplication | Shared bases, a common polynomial kernel and exact transport of the finite domains | Sparse domains do not become complete residue blocks; filling gaps lengthens the query | Finite support and clock range |
| Colour-free phase-kernel construction | One uniformly covered query with only O(sqrt k) starts, no colour enumeration | The clock grows to O(k^(5/2)); the current readout is soft O(N^(1/4)) | Coverage/compression tradeoff |
| Chirps, unconstrained twists and some fusion/deformation proposals | Some inexpensive operations or formal identities | Coverage or preservation of useful zeros fails, or is unproved | A different arithmetic predicate |

The [dated inventory](inventory.md) lists the individual reformulations,
their status and source locations. These groups are a dependency map,
not a count of independent algorithms. A new name or a determinant
identity is not counted as a new computational capability.

## Three concrete hybrid tests

### 1. Cheap moments plus the unique-hit locator

This pairing has real mathematical overlap. The moment construction can
be applied to the old torus polynomial itself, under its actual clock
guards. There is no need to pretend that the new scalar family inherits
the old uniqueness theorem.

For clock points x_i, write P(F)=product_i F(x_i). The two locator
outputs are its directional derivatives

    D_1 P = sum_i product_(r!=i) F(x_r),
    D_X P = sum_i x_i product_(r!=i) F(x_r).

At a unique simple hit x_I, their ratio is x_I. A full-support Hankel
determinant equals a unit times P(F), so its projective gradient gives
exactly this locator. That is a valid bridge between representations.

It does not initialize the bridge. The cheap moments weight F(x_i),
whereas the locator weights the product over every OTHER position.
Aligning the two actual weight systems gives

    (q;q)_m * sum_i x_i^s F(x_i)/G'(x_i) = 0,
    G(X)=product_(i=0)^m (X-q^i),  J+s<m.

Thus the direct candidate outputs for s=0,1 are BOTH zero even on a
good unique-hit input. The genuine locator denominator is nonzero.
Small Hankel minors instead contain sums over subsets. In the TQ
factorization, the useful derivative belongs to the retained long
product; differentiating only the cheap core omits it.

**Assessment:** a valid identity and a precisely located missing
operation. The projective derivative remains an interesting weaker
output specification; no computational separation from product
acquisition has been proved. [Derivation](moment-locator.md),
[independent review](review-moment-locator.md).

### 2. Cyclic resolvent plus the knot prefix consumer

The cyclic auxiliary model gives a cheap norm and a genuine inverse
action at small rank. The knot model gives a cheaply acquired degree-J
polynomial F, and the consumer only needs to know whether each requested
prefix has a nonunit. These appear complementary.

The exact Cauchy displacement bridge has rank at most J. After a paid
unit screen, a concrete J-dimensional correction acts by multiplication
by Q_m(T)/(T^m-1) modulo F, where Q_m is the finite physical clock
polynomial. Its determinant is

    Res(F,Q_m) / Res(F,T^m-1).

The denominator is a known unit, so this preserves the desired prefix
predicate. But at a native root v_a, its eigenvalue is

    Q_m(v_a)/(v_a^m-1).

The numerator is precisely the old long q-product. Both cyclic marginal
norms can be cheap while this interaction remains uncomputed. Choosing
a small auxiliary rank gives a rectangular bridge rather than an
invertible change of basis on the full clock. Choosing full rank makes
the direct inverse-action construction too large, or returns to the
same small uninitialized correction.

**Assessment:** this tested composition reaches the same acquisition
wall. It is not a lower bound for all implicit determinant algorithms.
[Derivation](topology-prefix.md), [review](review-topology-prefix.md).

### 3. Common scalar seeds plus coarse collision selection

The new phase-kernel construction genuinely trades colour complexity
for clock length. Its single acquired family is

    Z = product_(|b|<=V) product_(|h|<=W, h!=Cb)
                            (1-q^(Cb-h)),
    V=O(sqrt k), W=O(sqrt(N/k)+sqrt k), C=ceil(N/(2k)).

Coverage is uniform on the prepared hard branch. Every included leaf
has a nonzero known integer beta exponent, so localization retains the
existing recovery route. The guaranteed hit need not be unique. The
current readout is soft O(N^(1/4)), worse than the retained route.

Here there is a useful, fully costed hybrid target: acquire ONE residue
rho modulo k containing any useful hit h. Restrict every clock to
h=rho modulo k. Then

    number of starts * remaining clock length
        = O(sqrt k * (W/k+1)) = O(k^2).

The existing joint evaluator and recovery machinery now finish in
soft O(k). A polylogarithmic covering palette of residues would also
suffice. This needs neither a colour nor a unique hit nor an exact
collision position. Alternatively, supplying b plus a residue of h
modulo an O(sqrt k) modulus suffices in the hardest size regime.

**The supplier is missing.** The old coarse-factor-residue decoder is
another consumer, not an algorithm that supplies this clock residue.
Old index palettes refer to a different witness. Restoring torus
uniqueness adds a row-dependent torus factor and loses the common
scalar seeds. No current representation performs the required handoff.

**Assessment:** distinct advantages, with a concrete remaining bridge.
It is reasonable to investigate this special selector, but this audit
does not prove it cheaper than the original query. [Coverage and
composition](coverage-selector.md), [kernel construction](kernel-cover.md),
[review](review-coverage-selector.md).

## What really shares a wall

The finite q-product, its resultant, the full Hankel determinant, the
appropriate torsion norm, and the collision-bearing normalization of
the TQ model are exact forms of the same central scalar. Several
short representations expose that scalar without acquiring it.
The exact full-gradient interfaces also have product reconstruction
identities in the prior record. Merely swapping among these formulas
does not remove an unpaid operation.

This should not be overstated. A prefix bit or a successful projective
ratio is a weaker requested output. We have not proved it as hard as
the whole scalar. Similarly, explicit-support counts do not give
arithmetic-circuit or factoring lower bounds. The [shared-slice
audit](slice-union.md) only rules out shrinking the full current grid
to the target mass by literal integer-label merging. The [finite
multiplication test](shared-recurrence.md) only rejects its naive
large-envelope completion; sparse alternatives remain open.

Some gains already compose successfully. Signed Gauss coverage,
complete phase catalogues and scalar annihilator recovery improved this
route from soft O(k^(3/2)) to soft O(k^(5/4)). Knot realization and
prefix recovery compose exactly, though acquisition is still unpaid.
Common-character normalization and finite-domain transport also
compose, but do not by themselves reduce the scalar cost.

The research opportunity is therefore narrower than "combine every
representation": supply a missing selection or normalization operation
using information that another representation actually acquires. The
coarse kernel-clock residue is the cleanest new contract from this
audit; the projective first variation is the strongest exact bridge
among the existing readout formulations. Neither is solved here.

## Scope and validation

The three candidate investigations and their cross-reviews check
actual formulas, promises and costs. This is not an exhaustive test
of every pair in the inventory. The supporting kernel and slice
calculations are symbolic paper arguments, not Lean certificates.
All terminating saturated branches retain the inherited once-only
soft O(N^(31/192)) extractor cost. No numerical examples are used
as evidence of uniform coverage or a new exponent.

See [review record](review.json), [source pins](sources.json), and
[manifest](manifest.json). Earlier frozen reports and the existing
document prefixes are preserved; the audit is appended to the research
record. No new factoring implementation, Lean change, commit or push
is part of this audit.
