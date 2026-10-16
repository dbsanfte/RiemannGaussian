# Implicit norms, modular composition, and geometric-prefix products

Research date: 2026-10-15. Read-only repository investigation; all artifacts here are external to the repository. No universal lower bound is asserted.

## Main finding: sharper 2026 bound for a composite-ring primitive

Van der Hoeven and Lecerf, **Fast modular composition using spiroids**, author manuscript dated 12 August 2026, published Journal of Complexity 96 (1 October 2026), 102073, proves more than its finite-prime-field abstract suggests. Theorem 1, page 1, explicitly allows **Z/rZ for an arbitrary positive integer r**. Given monic H of degree D and explicit P,Q of degree <D, it computes P(Q) mod H in

    D^(5/sqrt(log D)) * softO(D log r)

bit operations. No factorization of r is part of the input. The algorithm lifts to integers, uses controlled floating-point FFT computations, and reconstructs exact results. This is a nearlinear, not softly linear, degree bound. We must not dismiss fast modular composition on grounds that the semiprime factors are unknown. Primary manuscript: https://www.texmacs.org/joris/fftcomp/fftcomp.pdf ; author HTML: https://www.texmacs.org/joris/fftcomp/fftcomp.html ; DOI: https://doi.org/10.1016/j.jco.2026.102073 . Local artifacts: spiroids.pdf, spiroids.txt, spiroids-page1.png (visually checked formula).

## Exact required reduction, not presently obtained

Put G_L(X)=prod_{0<=i<L}(X-u q^i). Then the required scalar S is

    S=(-1)^(JL) Res(F,G_L).

If one could compute g=G_L mod F in m^(1+o(1)) polylog(L) ring-bit cost, the remaining scalar resultant Res(F,g) is a standard small explicit resultant problem, with Euclidean inversions checked by gcd against N. Any proper nonunit pivot immediately factors N; unit pivots let the field-style arithmetic continue. Thus the useful missing contract is an **implicit q-Pochhammer remainder evaluator**, not a new general norm algorithm.

Exact desired contract: input monic F degree J, units u,q and binary L; return G_L mod F (or only Res(F,G_L)), or a proper factor of N, in (J log N)^(1+o(1)) polylog L bit operations. A weaker acceptable output is any scalar A whose reduction is zero in each hidden field whenever one target collision occurs there, together with a procedure yielding a proper separating gcd under the actual collision promise. Exact product output suffices. Merely retaining an all-targets collision does not.

The spiroid theorem takes **explicit coefficient arrays** of degree D, not a circuit representing a degree-L outer polynomial. Applying it directly to G_L requires reading/converting an L-coefficient object; it does not establish the contract above. Setting D=J does not permit pretending that the input G_L already has degree <J: that remainder is precisely the missing computation.

## Why moving carriers remain a live question

The obvious exact doubling identity is

    G_(2h)(X)=G_h(X) q^(h*h) G_h(q^(-h) X).

The two factors can be reduced mod F, but knowing G_h mod F does not determine G_h(q^(-h)X) mod F. Substitution X->q^(-h)X does not generally descend to R[X]/F. It instead transports the source to the quotient by the shifted polynomial F(q^h X), made monic. Consequently one can recurse on moving carriers, but the direct recursion branches into distinct shifted moduli. Fast modular composition makes an individual valid transport cheap; it does not remove the number or aggregate degree of carriers.

An endomorphism is available if the root multiset of F is stable under multiplication by the relevant q-power in both hidden fields (equivalently the shifted ideal agrees). In that special case repeated doubling plus fast composition really could close in nearlinear total cost. Generic independent targets do not supply that stability. This is an exact applicability condition, not a rank obstruction against arbitrary numeric q-squaring or implicit evaluators.

## Existing degree-sensitive bound

Bostan–Yurkevich, **Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications**, section 3.4/Theorem 5, explicitly accounts for growing degree. For scalar polynomial multiplier M(X) degree d and horizon L, choosing baby-block length b~sqrt(L/d) gives block degree db and L/b giant evaluations, for softO(d+sqrt(dL)) arithmetic cost. Taking M(X)=F(uX), d=J~m, L~m² recovers softO(m^(3/2)). Its fixed-order/fixed-degree softO(sqrt L) headline cannot be used with growing J at no charge. Primary full text: https://arxiv.org/html/2012.08656 ; publication DOI: https://doi.org/10.1016/j.jsc.2022.07.008 . For the polynomial-product specialization chirp evaluation needs powers of the unit q and no inverse Vandermonde differences; interpolation-based alternatives need separate unit checks.

## Other literature screened

* Kinoshita–Li, **Power Series Composition in Near-Linear Time**, FOCS 2024, Theorem 1: over any commutative ring, explicit f degree <a, g degree <n, f(g) mod X^n costs O(M(n) log a+M(a)). This is valuable and ring-safe, but is a truncation quotient, not arbitrary F, and still pays M(a) for explicit f. It does not give a succinct degree-L q-product remainder for free. https://arxiv.org/html/2404.05177v2 .
* Bostan–Flajolet–Salvy–Schost, **Fast computation of special resultants** (2006), computes composed sums/products and more general diamond products from root power sums. Its object is the degree-mn polynomial prod_(alpha,beta)(T-H(alpha,beta)). Producing the spectrum is larger than this scalar query. Specializing T=0 first requires a separate scalar-only complexity theorem; the cited result cannot be charged only the size of the one specialized coefficient. https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf .
* Van der Hoeven–Lecerf, **Fast computation of generic bivariate resultants** (2021), gives nearlinear finite-field Las Vegas computation under generic-position conditions, relative to the explicit bivariate problem size. It supplies no reduction of the binary-encoded geometric prefix to a size-O(m) generic bivariate system. https://www.texmacs.org/joris/resultant/resultant.pdf .
* Villard, **Elimination ideal and bivariate resultant over finite fields** (ISSAC 2023), improves elimination via structured polynomial-matrix reduction, quotient arithmetic, modular composition and transposed power projection. Its quotient-dimension dependence remains essential in the stated algorithm; the needed O(de) projections do not disappear when only a scalar is ultimately wanted. The finite-field genericity and leading-coefficient conditions also need factor-aware treatment over Z/NZ. https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/vil23.pdf .

## Candidate route worth pursuing

Exploit spiroid composition to investigate **batching moving-carrier remainders**, rather than rebuilding a single fixed quotient. A success theorem should bound the total representation size and total update cost for all carriers at every level by m^(1+o(1)) polylog L, while retaining the exact prefix. A falsifiable first target is a batch of K shifted moduli F(q^a X): compute all required transported residues in softO(J+K) or comparable nearlinear aggregate cost without first constructing a degree-JK product modulus. The plain product-tree approach pays JK and does not meet this target when K grows. No such theorem was found in the screened primary sources.

For ragged data normalize A_j=Y_j/u_j, so each row is a unit multiple of prod_(i<L_j)(A_j-q^i). Dyadic decomposition of each interval [0,L_j) gives O(J log Lmax) requested q-product evaluations at shifted unit points. This removes rectangular padding but leaves a multipoint implicit q-Pochhammer problem. Any purported improvement must charge this entire collection, preserve zeros in both hidden fields, and retain a refinement procedure when the total gcd is N. Knowing full-period norms does not compute arbitrary prefixes; replacing the prefix by an entire orbit may also introduce collisions outside the requested search region.

Conclusion: the new 2026 modular-composition theorem removes a genuine ring-model objection, but no nearlinear full query algorithm follows without an additional succinct q-product remainder/batch theorem. The exact growing-degree obstruction in the current constructive route is block degree Jb versus L/b evaluation count, not a universal impossibility theorem.

## Additional audit: determinism, strict target, and a concrete transport failure

The spiroid construction is deterministic as presented: its approximation precisions and rounded reconstructions are prescribed, and its algorithm does not choose random field elements or random projections. The only probabilistic algorithm mentioned in the introductory comparison is the distinct Neiger–Salvy–Schost algorithm. The new bound is **not softO(D log r)**: D^(5/sqrt(log D)) is superpolylogarithmic. It is D^(1+o(1)) times a nearlinear bit-size term. For every fixed epsilon>0 it is eventually O(D^(1+epsilon) polylog r), but that epsilon slack must be explicitly allowed. Even a successful reduction would therefore meet an almost-linear target first, not the strict soft-linear target requested here.

Here is an exact reason that a single residue plus a nearlinear composition primitive cannot implement the naive shifted update. Let c=q^(-h), and compare H_1=0 with H_2=F. They have identical residues modulo F. Their substituted values differ by F(cX) mod F. Unless F divides F(cX), they are different. Hence there is no well-defined map on R[X]/F sending the class of every H(X) to the class of H(cX). This argument is an information-loss statement for this proposed interface, not a prohibition on a richer implicit representation. The identity remains valid after reduction to either hidden field, where divisibility can be tested unambiguously.

Moving carriers avoid the logical failure by storing H mod F(X/c), but now the next doubling step requests further independently shifted carriers. The direct exact recursion has up to 2^t shifts at depth t; merging them by a product modulus has degree up to J*2^t. Coincident carriers or extra arithmetic relations can reduce this, so the degree count is an upper-bound accounting barrier for this construction, not a universal lower bound. BSGS balances growth against explicit evaluations and is exactly where the Jb + L/b cost reappears.

An augmented ring A=(Z/NZ)[X]/F does not make evaluating the scalar q-factorial free. A degree-one q-product with coefficient X inside A can be evaluated by the known softO(sqrt L) ring-operation algorithm, but each general A multiplication costs softO(J) base operations; this gives softO(J sqrt L), worse than the optimized base-ring BSGS bound. Taking a final norm is multiplicative and does not reduce those earlier A-operation costs. Truncated dual numbers A[epsilon]/epsilon^k can support derivatives or logarithmic reconstruction only after paying the larger coefficient dimension. Logarithms also invert collision factors and are invalid exactly at the desired zeros unless a separate division-free identity is proved. Neither augmentation alone supplies a polylog-step prefix evaluator.

## Small-resultant qualification and an additional multi-index check

The signed orientation is S=Res(G_L,F)=(-1)^(JL)Res(F,G_L). Computing a small explicit resultant over Z/N should be implemented factor-aware: a unit Euclidean pivot supports the ordinary next step, a proper nonunit gives the desired factor, and a zero pivot modulo N calls for the legitimate degree-drop/branch rule. This report does not assert that an arbitrary field implementation automatically gives a uniform fast arbitrary-ring resultant theorem. The decisive unresolved cost is already the preceding succinct remainder acquisition.

A separate potential use of multiple-term q-holonomic algorithms is to process the ragged endpoints L_j. It only saves work when they are endpoints of the same recurrence. For normalized targets a_j, the multiplier 1-a_j q^n changes with j. Putting all a_j into A=R[X]/prod(X-a_j) gives one recurrence over A but charges arithmetic on a J-dimensional algebra; requesting many indices additionally asks for many A-elements unless a new diagonal extraction theorem is supplied. Thus the multi-index theorem alone does not implement the desired diagonal collection P_(L_j)(a_j) in almost-linear total cost. This does not rule out a genuinely new diagonal batched q-difference algorithm.


## Historical correction and q-difference nonuniqueness

Composite-ring applicability itself is not first established by the 2026 paper. Its section 1.2 explicitly attributes to Kedlaya–Umans the more general setting (Z/rZ)[z]/theta(z), arbitrary integer r and monic theta. The new finding for this audit is the sharper explicit subpolynomial overhead and the concrete deterministic spiroid algorithm, not the first availability of unknown-factor composite-ring modular composition. A blanket field-only objection to the older KU method was already too restrictive.

For rectangular products, T(t)=prod_j prod_(i<L)(1-a_j t q^i) obeys B(t)T(qt)=B(q^L t)T(t), with B(t)=prod_j(1-a_j t), T(0)=1. These conditions are necessary but do not by themselves uniquely characterize T over finite fields or Z/NZ. If q has finite order r, invariant functions of t^r can multiply a solution without changing the equation, and suitable polynomial invariants can preserve T(0)=1. A degree bound can eliminate some such alternatives only after a separate proof. Coefficient recovery encounters q^k-1: a proper gcd yields a factor, but q^k=1 modulo N is saturation/removable singularity, not automatic factoring success.
