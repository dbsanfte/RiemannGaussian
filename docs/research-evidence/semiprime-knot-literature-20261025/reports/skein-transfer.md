# Skein / tangle compression audit, 25 October 2026

Scope: R=Z/NZ, q a unit with order >16k² modulo each prime factor, F monic of degree J=soft-O(k), h=Theta(k^1.5). Target P_h(X)=prod_{0<=i<h}(1-q^i X) mod F, or a useful factor/locator. No improvement on soft-O(J+sqrt(Jh)) was established. Literature theorems and elementary deductions are explicitly separated below.

## 1. Most constructive exact skein identities

**Primary source:** Frohman–Gelca, *Skein Modules and the Noncommutative Torus*, Trans. AMS 352 (2000), https://arxiv.org/abs/math/9806107 ; author PDF https://www.math.ttu.edu/~rgelca/torus6.pdf , Theorems 1–2. In the Chebyshev basis, writing E_v for slope v in Z²,

    E_v E_w = t^{det(v,w)} E_{v+w} + t^{-det(v,w)} E_{v-w},
    E_v=E_{-v}, E_0=2.

This identifies the torus skein algebra with the symmetric part of a quantum Laurent torus. T_n uses T_0=2, T_1=z, T_{n+1}=zT_n-T_{n-1}. The monomial image of E_(a,b) is t^{-ab}(L^a M^b+L^{-a}M^{-b}) in the paper's convention (check parameter convention when changing LM relation).

**Elementary constructive consequence (not a claimed paper algorithm):** Let v_n=v+nw and d=det(w,v). Then

    E_w E_{v_n}=t^d E_{v_{n+1}}+t^{-d}E_{v_{n-1}}.

Thus a SINGLE affine-slope family has a constant second-order recurrence retaining n as actual winding data. Given E_v,E_(v+w), one can advance symbolically by powering a 2x2 companion matrix in O(log h) operations in the relevant skein algebra. To turn that into soft-O(J), its entries must already act in a rank-O(J) algebra with soft-O(J) multiplication, and one must prove the output encodes the target locator. No identification of prod_i(1-q^i X) with one such curve was found. A product of affine-slope curves is a different object: repeated product-to-sum introduces many lattice slopes; two terms for a pair is not two terms for a long product.

**Primary source:** Lê, *On Kauffman bracket skein modules at roots of unity*, AGT 15 (2015), 1093–1117, https://msp.org/agt/2015/15-2/agt-v15-n2-p16-s.pdf , Propositions 2.1–2.2, pp.1098–1099:

    S(A_io)=R[u,u^{-1}],
    T_n(z)·e=t^n u^n+t^{-n}u^{-n},
    e·T_n(z)=t^n u^{-n}+t^{-n}u^n,
    T_n(z)·e-e·T_n(z)=(t^n-t^{-n})(u^n-u^{-n}).

These are exact two-monomial formulas with winding n. The paper's Theorem 1 and Proposition 2.5 characterize transparency/centrality through these expressions; nonconstant central threading requires appropriate root-of-unity parameters. The Chebyshev homomorphism of Theorem 2 assumes a root of unity. The generic formulas survive integral Laurent specialization; the root-of-unity collapse does not follow from large local order.

**Adaptation test:** The compressed powers are (tu)^n and their inverses. Our factors contain q^n X with exponent of X fixed at 1. Substituting u=X does not match; it produces q^n X^n. Substituting u with an n-dependent X^(1/n) is not an algebra homomorphism and is unavailable. The above affine-slope recurrence can compress sums of q^n X and q^-n X^-1, but does not compress the product of h such varying terms.

## 2. Exact reciprocal pairing, and its actual saving

The following elementary reciprocal fold is already established project material; it is included only to audit its relationship with the skein literature. For even h=2m, let c=q^{-(h-1)} and Y=X+c/X. Pair indices i and h-1-i. In R[X,X^-1],

    (1-q^i X)(1-q^{h-1-i}X)
      = q^{h-1} X [Y-q^{-(h-1-i)}-q^{-i}],

and therefore

    P_h(X)=(q^{h-1}X)^m
       prod_{0<=i<m}(Y-q^{-i}-q^{-(h-1-i)}).

This is a genuine half-degree representation invariant under X -> c/X after removing the prefactor. It preserves the geometric index through the displayed roots. It is evaluable in R[X]/F only when X is invertible, equivalently F(0) is a unit; otherwise one can clear Laurent powers, but cannot freely evaluate X^-1. Recovering inverse X costs soft-O(J) by monic reduction/extended gcd when F(0) is a unit. The remaining product has m=Theta(h) distinct geometric-clock roots in Y. It is not a Chebyshev polynomial except in additional special cases, and the half-degree change gives no asymptotic reduction. In particular, the classical sparse identity T_n(U+U^-1)=U^n+U^-n concerns root-of-unity/cyclotomic root patterns, whereas these roots are generic geometric orbit pairs.

There is no automatic inverse closure of the original catalogue: its uncentered exponent convention gives E'=H-E rather than -E. A direct centered trace target x+x^-1 for each original row is safe and has degree at most J. Explicitly adjoining inverse rows using i -> -i is also safe and has degree at most 2J. No J/2 quotient dimension is claimed. These are established project options, not new advances from the skein literature.

## 3. Twists and transfer matrices: compression does exist for repeated blocks

**Primary source:** Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. Math.126 (1987), 335–388, https://annals.math.princeton.edu/1987/126-2/p05 ; full paper https://ymsc.tsinghua.edu.cn/__local/3/3F/62/1293A0A1D1BE2BC710A48385251_F41A5764_34E7A6.pdf . The invariant is a Markov trace of a Hecke-algebra braid representation. Note 13.19 explicitly computes bridge presentations by matrices of Catalan size (2x2 for two bridges; 5x5 for three). Note 13.20 identifies the statistical-mechanical transfer-matrix connection.

**Elementary costs:** At fixed strand number n, TL_n has Catalan dimension C_n~4^n/n^(3/2); the full Hecke algebra has n! standard permutation-basis elements. A repeated braid block beta^h can be acquired from beta once, and its fixed d-dimensional matrix powered in O(d^omega log h) scalar-ring operations. Reading an arbitrary h-block word remains Omega(h). If each scalar is an element of R[X]/F, multiply these costs by the cost of quotient multiplication, soft-O(J). Thus constant d is attractive, but requires a proved map producing our exact output from a fixed block. Distinct spectral parameters q^i are not a repeated block.

**Primary source:** Champanerkar–Kofman, *On the Mahler measure of Jones polynomials under twisting*, AGT5 (2005),1–22, https://www.math.csi.cuny.edu/~ikofman/MJP-AGT.pdf , Section2 pp.5–7. TL_n has the crossingless Catalan basis over Z[A±1]. After extending to Q(A), the full twist decomposes into floor(n/2)+1 orthogonal central idempotents; its m-th power replaces eigenvalues by their m-th powers. Theorem2.2 uses this to express a fixed link with m full twists through a two-variable polynomial specialized at t^m. Their displayed twist normalization may suppress a global monomial, so use the paper's braid normalization consistently.

**Adaptation:** This is an excellent exact compression when long length literally means repeated full twists. The coefficients/eigenprojectors depend on the fixed outside tangle and strand number; they must be acquired, not supplied as an oracle. Rational projectors require denominators to be units after specialization. Integral crossingless multiplication avoids projectors but restores Catalan dimension. None of this makes the q-clock stationary.

**Primary source:** Champanerkar–Kofman, *On links with cyclotomic Jones polynomials*, AGT6 (2006),1655–1668, https://msp.org/agt/2006/6-4/agt-v6-n4-p03-s.pdf , Definition1/Proposition2.1 pp.1657–1658. For s open two-strand twist sites, the twist-bracket is a multilinear polynomial with 2^s smoothing terms, specialized at x_i=(-A^-4)^{n_i}. Proposition2.1 gives delta^s<L_n>=A^{sum n_i}P(A;x_1,...,x_s), delta=-A²-A^-². Their Example2 gives a second-order recurrence for two-bridge wiring diagrams, still with site-dependent x_i.

**Adaptation:** Fixed s gives compressed twist exponents; s growing with h incurs acquisition of up to 2^s coefficients. Dividing by delta^s is valid only if delta is a unit. The cleared identity is valid integrally. Choosing n_i=i embeds a geometric clock but creates h distinct sites, so the paper does not supply soft-O(J) advancement. The second-order wiring recurrence is nonconstant when x_i=q^i.

## 4. Burau determinant and fast topology algorithms

**Primary source:** Morton, *The Multivariable Alexander Polynomial for a Closed Braid* (1998), https://arxiv.org/abs/math/9803138 ; author PDF https://www.liverpool.ac.uk/~su14/papers/multiburau.pdf . The closed braid together with its axis has Alexander polynomial det(I-x B_beta), with reduced Burau matrix of dimension n-1. The colored/multivariable version is constructed directly from the braid word.

**Adaptation:** This determinant resembles prod_i(1-q^i X), realized by the explicit diagonal matrix diag(1,q,...,q^{h-1}); its dimension is h, so that representation alone gives no compression. To obtain a smaller Burau braid realization one must supply the braid word, prove equality of its determinant with the target modulo F, and count construction plus determinant cost. A determinant has x-degree at most n-1, so representing the unrestricted degree-h target in this form requires n-1>=h. Mod-F equality might permit smaller n but requires a separate constructive identity. Alexander normalization divides by 1+t+...+t^(n-1); symbolic divisibility does not authorize division by a zero divisor modulo N.

**Primary source:** Burton, *The HOMFLY-PT polynomial is fixed-parameter tractable*, https://arxiv.org/abs/1712.05776 ; full text https://arxiv.org/html/1712.05776v1 . Proves fixed-parameter tractability in diagram treewidth and a subexponential general-link algorithm; recalls Makowsky's earlier Jones treewidth result.

**Adaptation:** Bounded width controls boundary-state count, not length acquisition. A path/tangle representation with h distinct weighted crossings still processes h updates. A succinct repeated subdiagram could allow powering; proving such repetition is precisely the missing q-clock step. The paper does not establish polynomial time in log of a succinct diagram length.

**Primary source:** Wang–Wong, *Fast algorithm for multiplication on the skein algebra of one-hole torus*, https://arxiv.org/html/2405.20159v2 , especially Proposition5.5. Gives a recursion for discrepancy from the closed-torus Frohman–Gelca rule; time and space O(|det(v,w)|^6) in its stated arithmetic model. Published online 2025, Experimental Mathematics35(3)(2026),480–491, DOI10.1080/10586458.2025.2483946.

**Adaptation:** The result replaces crossing-resolution exponential behavior by a polynomial in geometric intersection. It is not polylogarithmic in winding/index and does not provide a near-linear algorithm for our long product. Introducing a puncture adds the boundary discrepancy term rather than creating an additional collapse.

## 5. Local cancellation / composite-ring audit

In TL conventions, put g_i=A1+A^-1 e_i with e_i²=delta e_i. Then g_i^-1=A^-1 1+A e_i, because g_i g_i^-1=1+(A²+A^-²+delta)e_i=1. This is a division-free local cancellation identity. The braid/Yang–Baxter relation g_i g_(i+1)g_i=g_(i+1)g_i g_(i+1) follows from the TL relations and changes order of three factors; it does not delete generic factors. A compression claim needs actual inverse pairs or a fully specified spectral-parameter telescoping identity with boundary terms. Products containing only (1-q^i X) do not have supplied inverse partners.

Every identity over Z[A,A^-1] can be specialized to R once A is a unit. If a desired convention needs a square root of q, that root is not given; avoid it by reparameterizing or use the finite free extension R[T]/(T²-q), explicitly counting the constant rank expansion. Rational semisimplicity, division by quantum integers, and interpolation denominators require gcd checks. For 0<r<=h (and generally r<16k²), 1-q^r is a unit by the stated local-order hypothesis. More general sums/differences of twist eigenvalues are not automatically covered unless their exponents fall in this range and differ in the correct form. A failed unit test can yield a factor, but cannot be assumed to do so on every input.

Duplicate of the existing Ore audit, recorded only for consistency: Df(X)=f(qX) and M_X satisfy DM_X=qM_XD; ((1-X)D)^h1=P_h(X). D usually does not descend modulo F. If both q-Weyl generators are invertible dxd matrices, determinants force q^d=1 modulo each prime. Thus a faithful finite free invertible q-torus representation has d at least the local order; this only excludes that specific lift. It is not a lower bound for every algorithm, noninvertible representation, or weak locator.

## Practical lead ranking

1. **Actual constructive candidate:** Match a desired weak locator with one affine-slope skein family, using the fixed second-order recurrence in Section1. This could retain index with bounded algebraic width; the missing equality is the substantive mathematical task.
2. **Established project material, no new priority:** Reciprocal pairing in Section2. Direct centered traces have degree at most J; explicit inverse adjunction has degree at most 2J. Neither supplies the missing fast advancement.
3. **Available under extra structure:** Repeated full-twist / repeated braid-block compression, provided a small fixed strand presentation and its coefficients can be acquired in soft-O(J).
4. **No established generic improvement:** Chebyshev root-of-unity transparency, bounded-treewidth scanning, Burau determinant, Yang–Baxter reordering, or punctured-torus polynomial multiplication by themselves.

No claim here proves that a novel skein-based weak locator is impossible. The exact published identities identify what must be matched and expose acquisition, dimension, and unit conditions that a proposed construction must pay.
