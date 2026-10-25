# Fresh recurrence literature audit, 2026-10-24

Outcome: no acquired primary-source theorem gives deterministic all-input soft(J+sqrt(h)) factor-or-zero for the supplied split degree-J polynomial. This is a search result, not a lower bound. Repository inspected read-only: tail of AGENTS.md and journal filenames/text searches. No repository edits or numerical examples.

## Primary sources and exact applicability

1. Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, JSC 2022/2023, [full text](https://arxiv.org/html/2012.08656), [publisher](https://doi.org/10.1016/j.jsc.2022.07.008). Theorem 3 assumes a field, q≠1, supplied recurrence and initial data, and nonvanishing leading recurrence coefficients at every needed index. Its O(M(sqrt(N))) bound fixes recurrence order and coefficient degree. Section 3.3 explicitly restores growing polynomial-matrix degree d: baby polynomial degree is sd, costing soft(n^omega d sqrt(N)); geometric evaluation also pays sd. Thus taking n=1,d=J does not justify degree-independent cost. Optimizing block size gives the familiar soft(sqrt(Jh)) scalar bound. No scalar determinant or gcd-only improvement is supplied. Algorithms 1–2 evaluate a single shifted geometric-root product in soft(sqrt(N)); these are useful after genuinely acquired support compression, below.

2. Wang–Yang–Zhong, *Polynomial reduction for q-holonomic sequences*, June 2026, [primary full text](https://arxiv.org/html/2606.07061). Theorem 2.4 characterizes summability over K(q)[x,x^-1] under gcd(a0(x),aJ(q^i x))=1 for every nonnegative i. Theorem 3.5 adds nondegeneracy and a specified q-reflection symmetry to produce a bounded-degree remainder. Neither theorem supplies a finite-prefix scalar evaluation complexity, a modular composite-ring specialization, or acquisition of terminal recurrence values. Their applications are identities and congruences. This genuinely recent paper therefore does not discharge the requested algorithm.

3. Bostan–Cluzeau–Salvy, *Fast algorithms for polynomial solutions of linear differential equations*, ISSAC 2005, [author PDF](https://mathexp.eu/bostan/publications/BoClSa05.pdf), Theorem 2. For an r×r polynomial matrix of degree at most d over a finite field, N>d and characteristic p>sqrt(dN)+1, the arithmetic bound is O(r² M(sqrt(dN))+r^omega sqrt(dN)). Rank or scalar output does not remove degree d in this theorem. Its extrapolation proof materializes sqrt(dN) scalar locations.

4. Bernstein–De Feo–Leroux–Smith, *Faster computation of isogenies of large prime degree*, [author PDF](https://velusqrt.isogeny.org/velusqrt-20200616.pdf), section 3. This gives geometric-root-product evaluation using acquired additive decompositions of the exponent index set. It supports an actual covering-set approach, not free compression of arbitrary supplied offsets.

The search included 2024–2026 q-difference/high-term/matrix-factorial/scalar-resultant literature; no newer applicable complexity theorem was identified. No assertion that this list exhausts all literature.

## A feasible conditional gcd-support algorithm: acquired q-chain compression

This is an independently derived restricted-input algorithm, not a claimed new published theorem or native all-input advance. It uses gcd support to eliminate multiplicities without dividing through hit factors.

Assume the supplied unit roots can be partitioned into K explicitly acquired chains
  C_c={a_c q^t:0≤t<ell_c}, sum ell_c=J.
For each prime p|N, the condition that some root in C_c equals q^i, 0≤i<h, is exactly
  a_c=q^u mod p for some -(ell_c-1)≤u≤h-1.
Indeed u=i-t, and every integer in this interval has such a representation. Hence define
  S_c=product_{u=-(ell_c-1)}^{h-1}(q^u-a_c), S=product_c S_c.
Then gcd(S,N)=gcd(product_{i<h}F(q^i),N), because N is squarefree and the two products have identical local zero supports. This claims equality of gcds, not equality of product residues.

Each S_c is a single geometric-root product of length h+ell_c-1, after a unit rescaling. Bostan–Yurkevich Algorithm 2 therefore acquires it in soft(sqrt(h+ell_c)) ring operations by multiplication and geometric evaluation, with only inversions of the known unit q; no hit denominator occurs. Cost soft(J+sum_c sqrt(h+ell_c))≤soft(J+K sqrt(h+J)), plus gcd bit costs. Taking the minimum with ordinary blocking is valid. K=O(1) gives the desired query scale; K=J gives no improvement.

Acquisition: sort the actual residues Y_j and locate exact qY_j matches. Since roots are units and pairwise separated, each vertex has at most one predecessor and successor. Local order(q)>J rules out cycles among J roots, so the exact edges give disjoint paths. Sorting costs soft(J) comparisons on O(log N)-bit integers. This method makes no assumption that a congruence modulo only one unknown prime can be detected by sorting: it uses only exact modulo-N edges. Fewer edges merely means a weaker compression, never a false certificate.

Restriction handling: root restrictions break paths into acquired subpaths. An index restriction that is a contiguous interval changes the exponent interval endpoints and leaves the same proof valid. A union of s disjoint index intervals expands to at most s intervals per chain; merge overlaps exactly before evaluating. Arbitrary restrictions need explicit interval complexity and cannot be claimed free.

Why this does not settle the native case: q=beta^(m²), Y_j=beta^(N+delta_j), with delta_j=O(m²), does not imply that most roots are adjacent under q multiplication. Distinct delta residues modulo m² can force K=J. Conversely, accidental modulo-N exact edges are fully usable. No deterministic native K=soft(1) bound or alternate bounded-chain covering theorem has been proved. This is a safe adaptive branch and a concrete structural research test, with all its acquisition costs paid.

The all-input target still requires a genuinely fused terminal evaluator or a new arithmetic coverage theorem. The canonical unrestricted complexity stays soft(m^1.5), and no N^(1/6) whole-controller claim follows here.
