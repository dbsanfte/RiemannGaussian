# Knot q-holonomic audit — 2026-10-25

Scope: acquired monic F of degree J=soft O(k), h=Theta(k^(3/2)), unknown semiprime ring, long local q-orders. No exponent improvement proved. Existing soft O(J+sqrt(Jh)) remains paid. This is a literature and adaptation audit, not an impossibility theorem.

## Most useful constructive finding: finite descendant boundary identity

Write t=x+x^-1, C_0(t)=1 and C_m(t)=prod_{j=1}^m(t-q^j-q^-j). These are exactly the Habiro cyclotomic kernels after Laurent normalization: a literature match, not a novelty claim. Their use and reciprocal folding are already known in this project and retain old project credit. The important audit question is whether the figure-eight knot's fixed-order descendant recurrence extracts C_M cheaply.

**Derived identity, valid over any commutative ring with unit q:** define the *finite* descendant

`D_m^[L](t)=sum_{j=0}^L C_j(t) q^(mj)`.

Then

q^(m+1) D_(m+1)^[L] + (1-t q^m) D_m^[L] + q^(m-1) D_(m-1)^[L]
 = 1 - q^(m(L+1)) C_(L+1)(t).

Proof: C_(j+1)=(t-q^(j+1)-q^(-j-1))C_j, so the summand of the left side is C_j q^(mj)-C_(j+1)q^(m(j+1)); telescope. This uses no division, roots of unity, knot assumptions, or genericity. Taking L=M-1 gives the required C_M from three adjacent finite descendants, with only soft O(J) extra work in the folded quotient.

**Constructive research recommendation:** seek three finite descendants at m=-1,0,1 modulo the folded catalogue in additive soft O(J+sqrt M) cost, or seek a linear combination whose initialization is cheap. The boundary identity gives an exact certificate to validate such a proposal. It avoids reliance on the analytic/completed infinite descendant. It does not itself make the three sums cheap: they have length M, and their truncation boundary contains the unknown C_M. Treating the infinite recurrence's right side 1 as valid for finite sums would erase precisely the target.

There is also an exact truncated generating polynomial A_L(u)=sum_{j=0}^L C_j(t)u^j. Its second-order q-difference equation has boundary C_(L+1)(t)u^(L+1). Thus coefficient extraction recasts the missing seed as the leading coefficient/boundary data. A short infinite generating expression alone does not initialize it over the general finite-ring quotient.

## Primary source for descendants and knot-dependent orders

Stavros Garoufalidis and Rinat Kashaev, *The descendant colored Jones polynomials*, arXiv:2108.07553v4 (2022), [paper](https://arxiv.org/abs/2108.07553), [full text](https://arxiv.org/html/2108.07553v4), §§2.2–2.5.

The source defines descendants by weighting the cyclotomic summand by q^(mj). For the figure-eight, Habiro coefficients are all 1 and equation (10) is the infinite/completed counterpart of the displayed boundary identity. Trefoil coefficients are a signed quadratic q-power; its descendant equation (7) has order two. For 5_2 the Habiro coefficient satisfies equation (13), order two, but descendant equation (14) has order five. A smaller span is proved using special negative-index relations. For twist knots K_p, equation (17) gives descendant order 3p-1 (p>0), and 3|p|-1 (p<0), versus colored-Jones order 2p-1 or 2|p|. These orders grow with the knot parameter. The examples therefore support exact elimination experiments, but not uniform bounded rank for growing catalogues.

**Assumption audit:** the infinite sums live in a colored Habiro completion; their specialization at x=q^n terminates. General acquired targets x=beta^E do not supply that termination. The finite identity above is safe at these targets. A method using infinite descendant initial values must construct them in the actual quotient and pay that cost.

## Habiro inverse: what coefficient extraction buys

Kazuo Habiro, *A unified Witten–Reshetikhin–Turaev invariant for integral homology spheres*, Invent. Math. 171 (2008), [arXiv:math/0605314](https://arxiv.org/abs/math/0605314), cyclotomic expansion and Lemma 6.1; the inverse is displayed explicitly as equation (3) of the descendant paper.

**Theorem:** the zero-framed normalized colored Jones sequence admits Laurent-integral, color-independent cyclotomic coefficients. Its inverse expresses the k-th coefficient using colors 1 through k+1, with q-factorial denominators before cancellation. Integrality is a property of genuine knot data.

**Derived application audit:** under the given order bound, short factors 1-q^r in the inverse denominator are units, so finite interpolation/inversion is executable over R after batch unit checks. It still asks for Theta(M) colors to recover coefficient M by the literal formula. Arbitrary input F does not become a fixed-knot colored-Jones sequence by this change of basis. For the figure-eight, inverse extraction gives its known Habiro coefficient 1, not the desired kernel C_M(t). Extracting the latter from the color dependence requires the same growing-degree coefficient/functional calculation. This distinguishes two indices that can otherwise look misleadingly interchangeable.

## Reciprocal fold and costs

**Already known exact identity:**

prod_{i=-M}^M(x-q^i)=(x-1)x^M C_M(x+x^-1).

**Correction to the initial symmetry premise:** the scalar catalogue uses 0<=lambda<H. Negating (a,b) and replacing nonzero lambda by H-lambda gives E'=H-E, not -E. Thus original inverse closure cannot be assumed. Explicitly adjoining x^-1 for each centered target x=beta^E, or retaining the negative lift -lambda, costs at most a factor two in row count and preserves the old cover. Global integer-zero deletion is invariant under E -> -E. A hit x^-1=q^i is exactly the original hit x=q^(-i); the centered window [-M,M] contains both indices. Map every added leaf back to the original row and index -i before invoking the old exact consumer, so every successful added leaf has the same valid arithmetic interpretation.

Alternatively construct the folded modulus directly with one Z=x+x^-1 per original row. Its hit Z=q^i+q^-i means (x-q^i)(x-q^-i)=0 in the relevant residue field, and each branch belongs to the original symmetric seed window. This may add mirror hits but loses no old hit. Over R, do not infer either branch globally from a product zero: use the existing gcd/localization machinery to split or select the local branch. The folded modulus has degree at most the original row count J, with possible duplicate Z values; there is no automatic J/2 bound. Only an actually inverse-closed catalogue with multiplicities and deletion handled permits that halving. The conclusion is a constant-factor reformulation, not a new exponent. Finite descendants modulo this folded quotient still incur the growing quotient cost unless a further compressed projection is found. Powers and conversion after a supplied folded answer cost soft O(J).

## q-holonomicity, AJ, and fast recurrence: known comparators

Garoufalidis–Lê, *The colored Jones function is q-holonomic*, Geom. Topol. 9 (2005), [arXiv:math/0309214](https://arxiv.org/abs/math/0309214), [author PDF](https://people.mpim-bonn.mpg.de/stavros/publications/holonomic.pdf), Thms 1–2 and §§4–5: every knot has a q-Weyl annihilator; order and initial-data bounds are exponential in crossing count; cyclotomic coefficients are q-holonomic. Effective creative telescoping can discover recurrences for a proper state sum. This supplies no cheap advancement theorem for a growing acquired order J. AJ/classical character-variety statements similarly supply no jump algorithm.

Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, JSC, DOI 10.1016/j.jsc.2022.07.008, [arXiv:2012.08656](https://arxiv.org/abs/2012.08656), Thm 5: field, order r, coefficient orbit-degree d>=1, nonsingular leading coefficients through n-1, n>d; cost O(r^theta sqrt(nd)+r² M(sqrt(nd))). This is **already audited comparator**, not a new route. The sqrt(n) headline fixes rank and degree. Rank-one evaluation in a degree-J quotient charges soft J per quotient operation. Fast scalar starts and one recurrence row do not supply fast transition products.

## Completion and quantum modularity

Habiro, *Cyclotomic completions of polynomial rings*, PRIMS 40 (2004), [arXiv:math/0209324](https://arxiv.org/abs/math/0209324), proves root-of-unity evaluation and Taylor uniqueness properties for cyclotomic completions. Here short cyclotomic factors are units under the long-order promise, rather than terminating zeros. These theorems give no exact finite-ring evaluator for the needed finite descendant.

Garoufalidis–Zagier, *Knots, Perturbative Series and Quantum Modularity*, [arXiv:2111.06645](https://arxiv.org/abs/2111.06645), presents root-of-unity perturbative matrices and a refined quantum modularity conjecture. No audited theorem converts this into an exact arbitrary-target selector over R. Asymptotic truncation and fixed-knot matrix ranks cannot be used as finite-ring exactness/cost bounds.

## Prioritized next steps

1. Use the finite-descendant boundary identity as a precise target: obtain three adjacent truncated figure-eight descendants at growing folded degree, with paid initialization. Investigate projected states, rather than claiming the infinite order-two recurrence initializes them.
2. Test a weaker selector obtained from a descendant linear combination, explicitly proving that boundary removal preserves the guaranteed hit and can be localized. A generic extra term can destroy zeros; no such selector is established here.
3. If trying knot families or inverse cyclotomic transforms, keep color, Habiro coefficient index, descendant index, and catalogue dimension separate. Require a bounded-rank theorem uniform in every growing parameter.

No claim of a solved 1/6 exponent or a lower bound is made.

## Scratch validation of the finite identity

Exact exhaustive modular checks passed for 326,592 choices of (N,q,t,L,m), with N in {15,21,35,77}, every unit q, every t modulo N, 0<=L<=7, and -3<=m<=3. This included 732 (N,q,t) cases whose C_0,...,C_8 list contains zero. These checks support the separate factor-by-factor telescoping proof; they are not a proof of a complexity improvement. Exact reproducer: `check_finite_descendant.py`; result: `validation.txt`, alongside this report. Source versions and inspection limits: `source-metadata.md`.
