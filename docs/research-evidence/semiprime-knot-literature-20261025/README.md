# Knot theory and the long collision query

25 October 2026. User-requested literature search, with three Sol 6.1
investigations. This packet identifies applicable algebra and specific
algorithmic questions. It establishes no new worst-case factoring exponent.
The current complete sixth-scale query remains soft O(k^(5/4)), with
k about N^(1/6); the desired soft O(k) acquisition remains open.

The closest match is **Habiro's cyclotomic kernel and the figure-eight
knot's descendant recurrence**. Reciprocal folding itself is old project
work. Identifying its kernel in knot theory supplies additional literature
and a precise finite boundary equation to investigate.

## Ranked sources and their actual use

| Priority | Source | Connection and outstanding task |
| --- | --- | --- |
| 1 | [Garoufalidis–Kashaev, The descendant colored Jones polynomials, §§2.2–2.5](https://arxiv.org/html/2108.07553v4) | The figure-eight descendants use exactly the folded seed kernel. Their finite recurrence retains the desired product as a boundary term. Acquire a suitable finite descendant projection cheaply. |
| 2 | [Frohman–Gelca, Skein Modules and the Noncommutative Torus, Theorems 1–2](https://arxiv.org/abs/math/9806107) | Product-to-sum identities compress individual curves along affine slope families into constant-order recurrences. Identify a native collision-preserving output with such a curve or matrix coefficient. |
| 3 | [Kato–Mizuno–Terashima, Quiver mutation sequences and q-binomial identities, Proposition 4.3 and (5.9)](https://arxiv.org/html/1611.05969) | Exact finite identities provide candidates for cancellation of q-binomial contractions. A transformation must reduce the full acquired computation, including its summation support and endpoints. |
| 4 | [Garoufalidis–Wheeler, A lift of the colored Jones polynomial of a knot (2026)](https://arxiv.org/abs/2603.01619), with [GSWZ, The Habiro ring of a number field](https://arxiv.org/abs/2412.04241) | Relative completions and finite congruence coordinates suggest a finite-jet formulation. A small jet determining the required high-order modular evaluation is not supplied by these results. |
| Secondary | [Kilic–Nijsten–Pellikaan–Ravagnani, Knot Theory and Error-Correcting Codes](https://arxiv.org/abs/2307.14882) | Fox coloring is an exact modular divisibility detector. A useful adaptation must acquire a coloring matrix and a proper factor witness cheaply. |
| Comparator | [Bostan–Yurkevich, fast q-holonomic evaluation](https://arxiv.org/abs/2012.08656) | Already audited in this project. The recurrence order and coefficient degree grow in our problem; the fixed-order square-root headline is insufficient. |

## Exact match to the current query

Use centered seed indices -M through M, so h=2M+1, and define

    C_0(Z)=1,
    C_M(Z)=prod_(r=1..M)(Z-q^r-q^-r).

For any unit x in any commutative ring with unit q,

    prod_(i=-M..M)(x-q^i)=(x-1)*x^M*C_M(x+x^-1).

Proof: each reciprocal pair is
(x-q^r)(x-q^-r)=x*(x+x^-1-q^r-q^-r).
This identity is division-free in Laurent variables, including at collisions.
C_M is the Habiro cyclotomic kernel when x=q^n, and remains a finite
polynomial for arbitrary acquired x. No root-of-unity assumption is used.

For the native list x_j=beta^E_j, acquire z_j=x_j+x_j^-1 and the monic
G(Z)=prod_j(Z-z_j) in soft O(J). Batch inversion is legal because x_j
are units. Duplicates may be retained. Screening x_j-1 handles the central
seed in soft O(J), using the existing global-annihilator consumer if the
gcd saturates. Computing C_M modulo G would then provide every remaining
row value through ordinary monic multipoint evaluation.

There is **no assumption that the stored catalogue is inverse-closed**:
its lifts satisfy 0<=lambda<H, and negation with lambda'=H-lambda gives
E'=H-E when lambda is nonzero. One may explicitly adjoin x_j^-1, at most
doubling the list, but it is unnecessary for the displayed per-row fold.
A mirror hit maps to the old seed index -i. The safe degree bound is
deg G<=J if duplicate nodes are removed, or exactly J with repetitions;
there is no automatic factor-two reduction in catalogue size.

At a prime dividing N, z_j=q^i+q^-i implies x_j=q^i or x_j=q^-i.
Globally those alternatives can differ between the two primes. Retain
the original row and test both signs when an index is recovered; a global
zero must not be treated as an integral-domain equality over Z/NZ.
Providing all full-window values alone still requires an interval
localization algorithm. The proposed soft bound must include shifted or
restricted calls, or return a useful label directly.

## A finite descendant identity with its boundary intact

For L>=0 and any integer m, set

    D_m^[L](Z)=sum_(j=0..L) C_j(Z)*q^(mj).

Direct telescoping gives

    q^(m+1) D_(m+1)^[L] + (1-Z*q^m) D_m^[L]
      + q^(m-1) D_(m-1)^[L]
      = 1-q^(m*(L+1))*C_(L+1)(Z).

Indeed the j-th summand is
C_j*q^(mj)-C_(j+1)*q^(m*(j+1)). This proves the formula over the actual
composite coefficient ring, and after reduction by any monic G.
With L=M-1 and m=0 it becomes

    C_M(Z)=1-q*D_1^[M-1](Z)
             -(1-Z)*D_0^[M-1](Z)-q^-1*D_(-1)^[M-1](Z).

The calculation is our finite adaptation of the figure-eight descendant
equation; no mathematical novelty claim is made. Obtaining these three
residues, or only their displayed combination, in soft O(J+sqrt(M)) would
meet the evaluation budget. Their current literal definitions still have
M summands. The infinite/completed descendant equation has right side 1;
substituting it here would delete precisely the unknown C_M. A low-order
recurrence does not provide its finite initial or boundary data.

This is the highest-priority computational target from this search.
The second candidate pairs its finite sums with the quiver-mutation
identities, seeking cancellation before dense coefficient expansion.
Both remain research proposals rather than algorithms with proved costs.

## Detailed audits and validation

- [q-holonomic, Habiro and descendant audit](reports/qholonomic.md).
- [Skein, twists, braid and transfer-matrix audit](reports/skein-transfer.md).
- [Quantum dilogarithm, quiver and recent relative-Habiro audit](reports/quantum-dilog.md).
- [Fox coloring and cyclic-resultant comparison](reports/alexander-coloring.md).
- [Source metadata](sources/qholonomic-metadata.md); the other reports give primary links and theorem locations in place.
- [Finite-identity reproducer](check_finite_descendant.py) and [its result](validation.txt).

The exact arithmetic check includes composite rings and vanishing factors;
it is a convention check, not evidence of coverage or an asymptotic rate.
The algebraic proof is the telescoping argument above. No Lean modules,
public theorem status, or generated explorer assets were changed. No
commit or push was performed for this literature pass. The source URLs
identify papers; only our reports and small validation artifacts are
archived here. The manifest fingerprints this packet's files, not the
external papers or every version of their proofs.
