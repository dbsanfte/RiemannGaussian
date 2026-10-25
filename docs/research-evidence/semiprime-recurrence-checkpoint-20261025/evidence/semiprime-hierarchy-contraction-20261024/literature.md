# Exact butterfly candidate: a supplied sparse inverse, not a paired-diagonal oracle

24 October 2026. This focused search found one new exact finite-field-compatible structural theorem and executed its natural recurrence reduction. The reduction is initialized and zero-safe but has length-L explicit input, so it does not improve the covered soft sqrt(JL) query. No new fast paired contraction or interpolation algorithm was obtained.

## New primary contract

Edgar Solomonik, *Sparse LDL, LU, and inverse butterfly factorization via tree decomposition*, arXiv:2504.20305v5, revised 1 July 2026:
https://arxiv.org/abs/2504.20305
https://arxiv.org/pdf/2504.20305
Cached `sources/solomonik-2026.pdf`, SHA256 `dd7a90c6e633253c3f59aba27436eb9c447a6db52a474422a0fe280ddf9f1ad8`.

Corollary 5.12 gives sparse LU over an arbitrary field from a supplied matrix and tree decomposition of its bipartite graph, with cost O((m+n) tau^(omega-1)); full LU at the same cost requires rank deficiency O(tau). Theorems 6.2 and 6.4 give exact complementary-rank O(tau) inverse structure and a butterfly factorization for invertible symmetric matrices of graph treewidth tau. Section 6 explains obtaining the factors from sparse LDL and extending through the symmetric embedding to nonsymmetric matrices. This is exact algebraic rank, not a numerical tolerance or analytic low-rank estimate. It assumes the actual sparse coefficients and graph representation; it is not a black-box matvec-to-selected-diagonal theorem.

## Execute on the actual zero-safe three-state recurrence

For actual supplied F and acquired direction polynomials U,V of degree O(J), use

    p_next=F(q^i)p,
    a_next=F(q^i)a+U(q^i)p,
    b_next=F(q^i)b+V(q^i)p,
    (p,a,b)_0=(1,0,0).

U=1,V=X gives the elementary-cofactor pair; the pre-existing row/class direction construction can instead supply the required label directions. No inverse of F(q^i) is used.

Let M_i be this 3-by-3 transition matrix. Form a block lower-bidiagonal matrix B of dimension 3(L+1), with identity diagonal blocks and block -M_i immediately below the diagonal. Then solving B s=(s0,0,...,0) gives the actual states, and two selected final coordinates are exactly the requested outputs. B is unit lower triangular even through hits, so its determinant is 1 over the actual quadratic composite ring. The symmetric off-diagonal embedding is also nonsingular. Adjacent time blocks give an explicit constant-width path/tree decomposition (constant-width after embedding too).

This is a valid application shape for the primary theorem, but n=Theta(L), not J. All F(q^i),U(q^i),V(q^i) can be genuinely acquired by polynomial MPE in soft(J+L), with the L q-clock points and O(L) sparse coefficients explicitly generated. The factorization/forward solve then costs O(L) up to logarithms. A direct forward pass already has this cost and is valid over any coefficient ring. Thus this executed exact-butterfly route charges soft(J+L)=soft k² at J~k,L~k²; it is slower than existing degree-aware blocking. Selecting only the last two outputs does not make the theorem's supplied coefficient list or graph disappear.

This is an input-cost audit of this reduction, not a lower bound on other graph realizations. An acquired O(k)-vertex bounded-width realization for the desired two outputs would be substantive new information. None was constructed here. Treating a polynomial-array node as one scalar graph vertex would require charging its actual coefficient algebra and elimination kernels separately.

## Relation to the paid hierarchy and paired matrix

The actual hierarchy source is `/tmp/semiprime-nested-alignment-20261024/nested-alignment.md`, SHA256 `fc96885e2ec89b08b939012777df8f542563a46bfea51667ed56a1eabd554216`. It acquires the canonical phase metadata, all level boundary unit corrections and aligned directions in soft k. It does not supply the native amplitudes. The exact point at each level is C D^h E^(h²); its mixed D and actual carries are retained.

The paid reshape action C and C^t on supplied vectors does not supply the diagonals

    v_R(y_j^b)^t C v_b(y_j),  bR~L,

or a sparse inverse realization of that paired operator with known small treewidth. In particular, the new exact-butterfly theorem cannot be applied merely because the input point labels have a hierarchy: its rank/separator property is a property of the ACTUAL matrix graph and inverse. The known modified-kernel commutator and its remaining terms are not dropped. No approximate butterfly rank, imported Fourier root of unity, or unacquired coefficient germ is substituted for them.

The new source removes a possible false blanket objection that all butterfly results are approximate: this one is genuinely exact over arbitrary fields, with its stated sparse-input contract. The natural fully acquired reduction above does not meet the target size. The covered restricted evaluator, original collision witnesses and bounded failure/fallback on unpromised labels remain soft(J+sqrt(JL)); no improved factor exponent follows.
