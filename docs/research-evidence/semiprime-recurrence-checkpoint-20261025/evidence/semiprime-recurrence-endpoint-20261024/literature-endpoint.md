# Scalar q-recurrence endpoint: primary-source degree audit and a tensor norm test

2026-10-24. Scratch only; repository read only. Target: E_L=prod_(0<=i<L)F(q^i) in R=Z/N, explicit degree J~m, L~m², with q a unit and 1-q^k certified units for k<=16m². Desired soft(J+sqrt L). No primary theorem checked here acquires that target bound; the strongest directly applicable initialized algorithm remains soft(J+sqrt(JL)). This is a scoped applicability conclusion, not an exhaustive literature claim or a lower bound.

## Directly applicable primary theorem, with degree restored

Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, [primary full text](https://arxiv.org/html/2012.08656), [publisher](https://doi.org/10.1016/j.jsc.2022.07.008). Theorem 5 is the relevant degree-sensitive statement: over a FIELD, recurrence order r, coefficient degree d in q^n, nonzero leading recurrence values at every required index, and index n>d, the bound is
  O(r^omega sqrt(n d)+r² M(sqrt(n d))).
Its scalar projection is already part of the theorem; taking one entry does not remove d. Our recurrence has order one, leading coefficient one and d=J. Therefore its specialization is soft sqrt(JL), not soft sqrt L. The discussion after Corollary 7 restores r,d for multiple requested endpoints: the good-degree tradeoff batches only about sqrt(L/J) endpoints at the same sqrt(JL) scale, plus logarithms. The displayed fixed-parameter Theorem 6 is not a degree-independent batch theorem.

The special scalar implementation also works over the composite ring without its field divisions. For b≈sqrt(L/J), explicitly acquire
  H_b(X)=prod_(a<b)F(q^a X), deg H_b=Jb,
then evaluate it at q^(bk), 0<=k<floor(L/b), multiply, and pay the short tail. Construction and monic MPE cost soft(Jb+L/b+J), giving soft(J+sqrt(JL)). No F(q^i), root difference or nonunit endpoint is inverted. Geometric evaluation can use q-unit chirp transforms; the stronger q-difference guard is not needed merely to legalize this product-tree route. Intervals and row restrictions have the same paid construction with their actual J and length.

## Scalar coefficient/projection algorithms do not initialize a new recurrence

Bostan–Mori, *A Simple and Fast Algorithm for Computing the N-th Term of a Linearly Recurrent Sequence*, [primary author PDF](https://mathexp.eu/bostan/publications/BoMo21.pdf), computes a term of a CONSTANT-coefficient recurrence of supplied order d in O(M(d)log N) ring operations. Equivalently, it extracts a coefficient of an acquired rational generating function. Its initial data/denominator must be supplied. E_(n+1)=F(q^n)E_n is q-variable-coefficient, so no order-O(J) rational generating function has been acquired. Constant-recurrence rational reconstruction or a black-box scalar sequence does not satisfy that input condition.

Bostan–Chyzak–Cluzeau–Salvy, *Low Complexity Algorithms for Linear Recurrences*, ISSAC 2006, [primary author PDF](https://mathexp.eu/bostan/publications/BoChClSa06.pdf), distinguishes compact recurrence representations from their evaluated high terms. Its matrix-factorial route assumes ordinary leading coefficients at the indices and retains degree/order costs. Compactly describing polynomial/rational solutions or transformed recurrences does not supply a cheap finite-prefix endpoint evaluation.

No scalar-only output lower bound is inferred from these sources: a different endpoint algorithm remains possible. The issue is what their actual algorithms take as acquired input.

## Resultants, modular composition and structured root sets

**Special resultants.** Bostan–Flajolet–Salvy–Schost, *Fast Computation of Special Resultants*, JSC 2006, [primary author PDF](https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf). Theorem 1 computes composed products/sums of degree-s and degree-t monic inputs with output degree D=st, using O(M(D)) field operations in characteristic zero or >D. Its more general diamond product is a characteristic polynomial in a rank-D tensor quotient; Proposition 3 acquires K power projections in O(sqrt(K) M(D)+D K^((omega-1)/2)) operations. These are not scalar constant-term algorithms with cost O(s+t). Characteristic and multiplicity qualifications matter when translating Newton sums back to coefficients. Their fast explicit-output results do not give a compressed resultant value for free.

**Fast modular composition, latest checked version.** Neiger–Salvy–Schost–Villard, *Faster modular composition using two relation matrices*, ISSAC 2026, [primary author PDF](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/comp2.pdf), [DOI](https://doi.org/10.1145/3815436.3815451). Theorem 1.1 takes explicit modulus degree n, bivariate degrees (u,d) with ud=Theta(n), and generic composition input; it costs soft(u d^((omega+2)/3)). Theorem 1.3 gives generic univariate composition soft(n^((omega+3)/4)). The nonempty Zariski-open condition is checked with failure possible. Neither theorem takes an implicit q-factorial remainder as input or computes it from an order-one equation. Applying it at degree sqrt(JL) does not improve already quasi-linear polynomial/MPE work there.

**Finite-ring near-linear composition.** Kedlaya–Umans as analyzed in van der Hoeven–Lecerf, *Fast multivariate multi-point evaluation revisited*, [primary PDF](https://www.texmacs.org/joris/kucomp/kucomp.pdf), genuinely permits rings (Z/rZ)[Z]/theta with theta monic. Unknown factorization of N is therefore not itself a reason to exclude this route. The degree/input size still counts: composition in a rank-L quotient is L^(1+o(1))-scale, and materializing L coefficients costs L. A short circuit for a huge polynomial is not the coefficient-vector input to that theorem. Near-linear exponents must not be rewritten as soft-linear bounds silently.

**Scalar projections in bivariate elimination.** Villard, *Elimination ideal and bivariate resultant over finite fields*, [primary PDF](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/vil23.pdf), uses transposed modular composition/power projection to compute the largest Sylvester invariant factor. The stated (de log q)^(1+o(1)) bit complexity is Monte Carlo over a KNOWN finite field, with explicit bidegree bounds d,e; resultants require the corresponding regularity/genericity conditions. This is an important selected-output algorithm, but de is the relevant quotient-size parameter, and its field/randomization hypotheses are not supplied here. A cheap projected sequence is derived from paid quotient arithmetic, not an assumed implicit endpoint oracle.

**Geometric-root evaluation.** Bernstein–De Feo–Leroux–Smith, *Faster computation of isogenies of large prime degree*, [primary PDF](https://velusqrt.isogeny.org/velusqrt-20200616.pdf), section 3 gives a uniform composite-ring geometric-root product evaluator in soft sqrt L at ONE scalar target, with only known-unit root powers inverted. Applying it at J arbitrary targets separately costs soft(J sqrt L), or ordinary global blocking balances to soft sqrt(JL). Its supplied index decompositions do not imply that J target evaluations can be multiplied at additive cost J+sqrt L.

## Duplicate guards checked in the repository

Read AGENTS.md and the main semiprime journal with targeted searches. Bostan–Caruso–Schost p-curvature uses a complete characteristic orbit, not this arbitrary prefix. The Tal TR26-211 entry concerns a conditional common-root Jacobi/CM reconstruction at q^(O(1)), not a uniform soft-q modular factorial query; its source/order promises are explicitly absent on some prepared branches. Known-prime-field roots, factored local group orders, and a high-order scalar image cannot be imported from the unknown factors. A logspace or compact-output representation does not itself bound time. Earlier adjoint/logarithmic jets, far Toeplitz/Schur determinants, q-Gosper residuals, q-chain support compression, and unstable endpoint quotient charts remain previous attempts, not discoveries of this pass.

## Distinct concrete transformation to test: a sparse diagonal tensor norm

This is an elementary rearrangement, not a claimed new theorem or a finished faster algorithm. Its distinction from the old degree-J companion/far-boundary formulation is that BOTH moduli have degree about sqrt L and are explicitly acquired; the endpoint is one sparse diagonal-polynomial norm in their tensor quotient.

Choose s=ceil sqrt L, t=floor(L/s), and separate a remainder of length <s. Define
  A_s(X)=prod_(a=0)^(s-1)(X-q^a),
  B_t(Y)=prod_(b=0)^(t-1)(Y-q^(s b)).
Both are acquired by product trees in soft(s+t), with no collision inverses. Put
  Q=R[X,Y]/(A_s(X),B_t(Y)), rank D=st,
  H(X,Y)=F(XY)=sum_(j=0)^J f_j X^j Y^j.
H is given by J+1 diagonal coefficients, not a dense J-by-J array. Powers exceeding the two degrees can be reduced by monic division, but their expanded reduced table is not declared acquired at small cost.

The exact endpoint identity is
  E_(st)=Norm_(Q/R)(H)
        =Res_Y(B_t(Y), Res_X(A_s(X),F(XY))).
It follows either from evaluating the two separated monic root sets or from multiplicativity of determinant of multiplication in a finite free algebra; it is an integral polynomial identity and remains valid at local hits. The leftover factors are an actual O(s)-point polynomial evaluation costing soft(J+s), not an omitted long tail.

All input objects here cost soft(J+s+t)=soft(J+sqrt L). The multiplication operator is F(C_A tensor C_B); the TWO companion matrices are implicit through their acquired O(s+t) coefficient lists. Writing its D-by-D matrix is not part of initialization. Likewise, the inner resultant has Y-degree at most Js and costs Js coefficients if explicitly formed. Known special-resultant machinery may first construct the composed product A_s tensor B_t of degree st, which is exactly the q-prefix root polynomial; that costs D, not s+t. These are real stopping points.

### Executable algebraic test target, with a lawful fallback

Test whether the nested Sylvester elimination can be performed for its FINAL SCALAR using closed displacement generators rather than constructing the degree-Js inner resultant. The Sylvester matrix in X has size s+J, and its F(XY) entries have the special form f_j Y^j; the other operand is the acquired geometric-root A_s. The outer modulus is the separately acquired geometric-root B_t. A candidate must explicitly maintain a small generator under the required fraction-free Schur complements or provide a guarded inverse rule returning a proper factor when a pivot is nonunit. It must charge generator growth and all arithmetic modulo B_t, whose rank is t~sqrt L. Treating one such quotient operation as one scalar operation would erase an unpaid factor t.

A precise success condition is a deterministic factor-or-norm routine
  (A_s,B_t,diagonal f_0,...,f_J) -> Norm_Q(F(XY))
with soft(J+s+t) TOTAL R work, including restrictions and nonunit handling. An exact determinant identity or a small initial displacement rank alone does not meet this condition; closure of the generator representation under elimination is the new statement to prove. This is a concrete structured elimination experiment, not an endpoint oracle added as an assumption to a factoring backend.

If generator closure fails or expands, the safe fallback is the already initialized original blocking algorithm at soft(J+sqrt(JL)); do not form a rank-D tensor table merely to claim progress. No numerical examples or empirical rank claims are used here. The transformation supplies a different fully acquired small input and a sharply specified algebraic test, but no improved endpoint exponent has been obtained.
