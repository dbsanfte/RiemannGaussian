# Knot constructions for the complete collision family

25 October 2026. Follow-up to the [knot literature search](../semiprime-knot-literature-20261025/README.md),
with three Sol 6.1 investigations and independent algebraic reviews.

The positive result is an explicit, inexpensive **Seifert matrix for the
whole native family**, coupled to a precise scalar prefix decision problem
that suffices for factor recovery. The matrix is constructed in soft O(J),
where J=soft O(k) is the number of retained rows. The long prefix decision
is still unpaid at that rate. The complete query remains soft O(k^(5/4)),
or soft O(N^(5/24)) at sixth-root scale; the deterministic all-semiprime
soft O(N^(1/6)) objective and complete executable/Lean bit proof remain open.

## A genuine knot representation with acquisition charged

After the existing central gcd screen, every acquired x_j and x_j-1 is a
unit modulo N. Define

    G(Z)=prod_j(Z-x_j-x_j^-1),
    f(w)=G(w+2)/G(2)=1+sum_(i=1)^J f_i w^i.

The denominator is a unit because 2-x-x^-1=-(x-1)^2/x. Product trees and a
division-free balanced Taylor shift acquire f in soft O(J) ring operations.
Lift its coefficients individually to integers of O(log N) bits.

Let Q be the J-by-J upper shift, E=diag(f_1,-f_2,f_3,...), and F=e_1 e_1^T.
The explicit integer matrix

    V=[[E,Q],[Q^T-I,F]]

has at most 4J-1 nonzeros, constant bandwidth after interleaving, and
V-V^T=[[0,I],[-I,0]]. Its determinant satisfies the exact identity

    T^-J det(V-T V^T)=f(T+T^-1-2).

The classical Seifert realization theorem makes this an actual knot
Alexander polynomial. Modulo N it equals

    Delta(T)=G(T+T^-1)/G(2).

This construction includes every retained row, arbitrary repeated nodes,
and all allowed semiprimes on the continuing branch. It does not require
inverse closure of the uncentered catalogue. The acquired object is a sparse
integer Seifert matrix; expanding its large binary twist parameters into
individual crossings could be expensive and is not part of the algorithm.

The [construction and proof](alexander-realization.md) include primary
Seifert and Kondo sources, the alternative unknotting-number-one realization,
integer-lift costs, and an [independent algebraic review](alexander-independent-review.md).
This is a faithful representation result, with no claimed new topological
realization theorem or factoring exponent improvement. General Alexander
realizability does not itself impose extra arithmetic constraints on G.

## A weaker operation would suffice

For every unit t,

    Delta(t)=prod_j (x_j-t)(x_j-t^-1)/(x_j-1)^2.

Therefore deciding whether

    A_m=prod_(i=1)^m Delta(q^i)

is a nonunit is exactly deciding whether any row collides in the signed
prefix [-m,m], after central screening. All displayed denominators are
already units; no q-factorial normalization is needed for this equivalence.

Coverage supplies a nonunit final prefix. Prefix nonunitness is monotone,
so logarithmically many Boolean prefix queries locate the first nonunit
index. Scanning the original rows at its two signs then yields a proper
gcd or a nonzero global exponent relation for the existing licensed extractor.
The complete proof handles saturated aggregates and different CRT signs.

The actual retained swap coverage also guarantees A_M=0 modulo N. Under
that stronger promise, a **zero-only prefix decision** suffices: at the first
zero prefix, the preceding prefix is nonzero, so the new factor must be a
nonunit. The same signed scan then works. Earlier prefixes may be nonzero
zero divisors; the proof does not silently assume they are units.

Thus a soft O(J+sqrt(m)) **prefix zero or nonunit decision** would suffice. It need
not return full remainders, descendants, a coloring basis, or a shifted-window
oracle. See the [consumer theorem and cost contract](prefix-query.md) and
[independent review](prefix-consumer-review.md). This specializes the old
weak-selector/bisection machinery; it does not supply the fast primitive.

Setting F to zero makes the Seifert determinant a unit, so each individual
Delta(t) is a rank-one correction. Across m distinct evaluation indices,
however, the evident construction has m independent corrections. The
remaining task is to exploit their shared input without expanding that
long product. No cross-index cancellation is proved by sparsity alone.

## Other representations tested

The [finite Pfaff/Heine analysis](quiver-contraction.md) provides the
collision-preserving normalization

    H_m(Z)=(-1)^m q^(m(m+1)/2) C_m(Z)/(q;q)_m^2,
    C_m(Z)=prod_(i=1)^m(Z-q^i-q^-i).

All scalar denominators are units under the existing local-order promise.
Its endpoint scalar normalization can be acquired with ordinary scalar
q-factorial baby-step/giant-step in soft O(sqrt(m)); that does not acquire
the whole-family H_m. A finite Pfaff identity expresses H_m as a weighted
descendant sum. Heine's third transformation cancels its generating-function
prefactor exactly to 1/(1-v). The resulting order-two q-difference operator
is valid to finite precision over the composite ring, with its desired
coefficient retained as the boundary term. Coefficient decimation grows
the parameter lists; a bounded-width doubling rule has not emerged.

One specific initialization route is now excluded on the **actual full
native family**. The [raw Green/Padé analysis](descendant-advance.md),
[native-axis count](native-axis-review.md), and
[weighted Padé review](weighted-pade-review.md) show that rational
generators with numerator/denominator degrees soft O(J) cannot match
precision M=Theta(k^(3/2)) on the entire acquired quotient, for sufficiently
large continuing inputs. The retained native axes supply components that
cannot terminate at those degrees. This excludes that bounded-degree
rational ansatz, including the normalized variant, rather than all compact
states, weaker selectors, alternative pruning, or fast algorithms.

The [skein selector attempt](skein-selector.md) audits a concrete
width-two discriminant matrix: it works modulo the known k^2 but loses the
needed discriminant modulo N. The [quantum modular reciprocity audit](modular-reciprocity.md)
keeps the exact correction terms in Bettin–Drappeau's transformation;
known root orders and analytic corrections are not supplied modular inputs.
Neither failed candidate is a general impossibility result.

The [partial torsion and gluing audit](partial-torsion-leads.md) tests three
further primary sources. A genus-one Dehn shear records q^i with constant
topological boundary size, but changes its boundary character at every step.
The resulting formal scalar transfer still contains the original partial
product. Open-shift and cyclic-closure constructions likewise do not supply
the required truncated geometric spectrum. These calculations identify a
concrete target for a new gluing identity, without claiming a general barrier.

## Papers worth carrying forward

| Source | Applicable content and boundary |
| --- | --- |
| [Seifert, Über das Geschlecht von Knoten, Satz 5–6, pp. 587–589](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/seifert.pdf) | Constructive realization under the standard skew condition; supports the acquired sparse matrix. |
| [Kondo, Knots of unknotting number 1 and their Alexander polynomials, Theorem 3, (8)](https://ir.library.osaka-u.ac.jp/repo/ouka/all/6492/ojm16_02_19.pdf) | Entire family also admits an encoded unknotting-one realization; this alone does not shorten the partial product. |
| [Garoufalidis–Kashaev, The descendant colored Jones polynomials](https://arxiv.org/html/2108.07553v4) | Exact kernel match from the earlier packet; finite boundaries and initialization remain essential. |
| [Kato–Mizuno–Terashima, Quiver mutation sequences and q-binomial identities](https://arxiv.org/html/1611.05969), with [Dhar, Pfaff's Method Revisited](https://arxiv.org/html/2405.08705) and [DLMF 17.6.8](https://dlmf.nist.gov/17.6.E8) | Finite cancellation and an exact rational gauge transformation; summation support remains charged. |
| [Bettin–Drappeau, Modularity and value distribution of quantum invariants of hyperbolic knots](https://arxiv.org/abs/1905.02045) | Exact analytic reciprocity suggests a direction, but neither finite-ring correction acquisition nor unknown-order specialization follows. |
| [Florens–Massuyeau, A functorial extension of abelian Reidemeister torsions](https://arxiv.org/abs/1403.4050); [Bigelow–Cattabriga–Florens, Alexander representation of tangles](https://arxiv.org/abs/1203.4590); [Borghini, A gluing formula for Reidemeister–Turaev torsion](https://arxiv.org/abs/1401.0431) | Exact boundary and tangle composition. The desired extension must retain changing characters and acquire the scalar/gluing corrections cheaply. |

The constructive next target is a partial Alexander-product decision or an
equivalent tangle/coloring calculation satisfying the prefix cost contract.
Use the native arithmetic where needed; a theorem for arbitrary reciprocal
polynomials is stronger than the objective requires. Additional backend
lemmas or successful example coverage do not pay for this operation.

## Validation and provenance

- [Sparse determinant check](check_alexander.py): 280 exact determinant
  comparisons, standard skew part, and sparse-entry count;
  [result](alexander-validation.txt).
- [Finite identity check](check_quiver.py): rational polynomial identities,
  quotient reductions, retained boundaries, decimation and trace norm;
  [result](quiver-validation.txt).
- [Prefix consumer reference check](check_prefix_consumer.py): eight
  nonunit-prefix and five zero-only CRT control-flow fixtures, with eighteen
  exact norm comparisons;
  [result](prefix-validation.txt). Its oracle is deliberately slow and the
  fixtures do not assert native coverage or a scaling rate.

The algebraic proofs establish the statements; finite checks catch signs
and control-flow errors. No Lean or generated proof-status assets changed.
The earlier literature packet and archived recurrence checkpoint are
preserved byte-for-byte. Legacy scratch paths inside reports refer to work
now archived under
`../semiprime-recurrence-checkpoint-20261025/evidence/`; external full papers
and page images remain scratch-only and are not redistributed here.
See [review.json](review.json) and [manifest.json](manifest.json) for the
scope and fingerprints. This is local research; no commit or push performed.
