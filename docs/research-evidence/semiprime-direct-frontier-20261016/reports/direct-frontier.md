# Direct acquisition search: no improved query bound

2026-10-16. Three existing Sol 6.1 agents ran parallel primary-literature
and arithmetic investigations. This pass found neither a restriction-stable
soft O(m) collision query nor a new obstruction. It does not extend the
preceding native-center carrier theorem. The general soft O(J+sqrt(JL))
bound, hence soft O(m^(3/2)) for J~m and L~m^2, is unchanged.

## The missing operation

Write F_L(X)=product_(0<=i<L)(1-q^i X). The actual row family supplies
J~m public nodes z_j; its collision information is in F_L(z_j).
Fast coefficient-block actions, transposes and square-block inverses are
already paid. They do not themselves construct the paired substitution
of the implicit block polynomial modulo the row locator.

A successful replacement must acquire row values or an equivalent
factor-producing query in soft O(J+sqrt L), including its seed and node
costs. It must work on restrictions to tag subsets and contiguous seed
intervals, or supply another equally cheap treatment of saturated products.
A norm that vanishes modulo BOTH hidden factors is not by itself a proper
factor. The full bit/controller and Lean composition would still remain.

The weighted-scalar alternative remains attractive: a constructed
soft O(m) arithmetic circuit for sum_j w_j F_L(z_j), with formal weights,
could be differentiated to recover all row values. No such circuit was
constructed. Expressing the sum as a matrix trace leaves the trace unpaid;
a fast matrix action and an inverse for one coefficient block do not
construct the needed determinant deformation. This is no operation lower
bound.

The proposed Hankel/Christoffel norm reduction also leaves the values
unpaid. For a measure on exactly L geometric points, its degree-L monic
orthogonal polynomial is the grid polynomial itself. The resulting small
alternant contains that polynomial evaluated at the row nodes. Writing a
smaller determinant has not acquired its entries. These are outcomes of
specific attempts, not impossibility results for other trace/norm methods.

## Recent primary algorithms and their input contracts

Neiger--Salvy--Schost--Villard,
[Faster modular composition using two relation matrices, v2](https://arxiv.org/abs/2601.17422v2),
accept coefficient-supplied composition data with stated field/genericity
conditions. The supplied fast q-coefficient action is not that data, and
this pass found no paid conversion. Berthomieu--Neiger--Passe,
[Computing submatrices of the Hermite normal form of a structured polynomial matrix, v2](https://arxiv.org/abs/2602.08027v2),
require polynomial displacement generators for their specified displacement.
The available generalized q-pencil has not been converted to those
generators for the required remainder or composition map. Neither input
mismatch is a theorem ruling out a succinct extension.

Yann Tal's September
[Computing Modular Factorials Below the Square-Root Barrier](https://eccc.weizmann.ac.il/report/2026/211/)
has a deterministic theorem for KNOWN prime p and supplied divisor v|(p-1),
with cost soft O(v^c+sqrt(p/v)), for an unspecified absolute c>=1.
Its higher-cyclotomic supplied-data theorem uses a finite-field
representation and compatible character; constructing those can instead
be Las Vegas. Thus calling every result randomized would be incorrect.
The scale is p, not just the interval length. Section 1.4's composite
extension assumes the prime-power factorization is given. Guarding scalar
inversions by gcd does not supply its missing characteristic-dependent
data. No geometric-factorial or growing-degree locator-norm reduction was
found. This is an applicability audit, not a general obstruction.

The source PDFs inspected are pinned in sources/primary-pins.json. They
are linked rather than reproduced here. No full proof certification of
these papers is claimed.

## Official OpenAI/math snapshot

The old pinned revision adc7f1241b42e322a6451854ab7e4b4c146bf78a has
advanced to 1581d4cbdd69a0faf34b2089614fe2a814316a6a. The complete
preprints subtree comparison has 381 added, 6 modified and 31 removed
blobs: 418 touched files in 30 folders. The large top-level recursive
tree and compare file list were truncated and are not used as complete
inventories. This record does not claim that the whole repository is
unchanged.

All 62 blobs in the selected Quasi-RH, prime-field polynomial factoring,
primitive-root, simultaneous-primitive-root and exact-quantum-factoring
families are identical at the two pins. The NumberTheory, Algebra,
LinearAlgebra and RingTheory OAI subtree hashes are identical too. Thus
there is no changed arithmetic algorithm in THOSE checked families.
The [repository history at the new pin](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/history.md)
reports three Hodge-paper withdrawals, fourteen repairs, thirteen
dependent-reference updates and 300/719 top-line formalizations. Those
are repository reports, not independent build or theorem certification.
The preceding carrier proof uses its published classical prime inputs.

The exact Logspace Equality/Deterministic sources were also inspected.
Their exported class-membership equality supplies no exponent-preserving
time relationship. In binary input length ell=log N, an N^(1/6)-time
algorithm is not automatically a polynomial-time BPL witness. Padding
does not preserve that exponent without a separate quantitative proof.
See repo-delta/logspace-scope.md. No factoring reduction was acquired.

Run `python3 repo-delta/check.py` from this evidence directory. The
standard-library checker reconstructs complete preprint Merkle trees,
links them and four unchanged OAI subtrees to the saved repository trees,
and checks the saved history and two logspace source blobs. Its certificate
records the official API snapshot; Git hashes check internal consistency,
not signed remote authentication. It neither runs Lean nor verifies the
mathematical claims. An independent review checked these exact limits.

No new native code, Lean lemmas, examples or broad builds were added.
The next substantive advance still needs an actual paid acquisition
algorithm or a new arithmetic obstruction to a specified route.
