# Exact exotic finite forms: fermions, supercharacters and weighted graph zeta

26 October 2026. Paper-only symbolic/algorithmic experiments, using the frozen [even-acquisition interface](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-even-acquisition-20261026/README.md). No repository edits, tests, numerical campaign or implementation.

**Result.** Four exact finite forms are mapped below. Two stronger contractions are executed: a rectangular supercharacter gives a J-dimensional determinant but its entries require the unacquired clock remainder; weighted Bass–Ihara gives a (J+h)-vertex operator whose diagonal residues ARE the desired block counts, but whose Cauchy denominators are already the original singular input. Neither is a paid soft-K evaluator. The graph construction additionally admits an exact tensor reduction to two rank-one-perturbed diagonal operators. This supplies a concrete new structured identity, not an acquired determinant or zero predicate.

## 1. Shared input and four finite mathematical forms

Let d=Jh, u_i=rho^i, w_ji=T_j*u_i and

    P=product_(j,i)(1-w_ji).

T_j=q^M0*y_j is the ACTUAL normalized root; no physical endpoint is shifted silently. Rows include their original labels, canonical squared tags and sign-invariant singleton blocks. An admissible block residue may have any nonzero amplitude at its sole good hit. Clock differences through 16H are actual units. Repeated rows remain a multiset.

1. **Fermionic partition function / exterior Gaussian.** On d independent Grassmann pairs with mass diagonal D=diag(1-w_ji), the top coefficient of product_(j,i)(1+(1-w_ji)barpsi_ji psi_ji) is det D=P. The diagonal source observable is Tr(C(D+delta I)^-1), with C_ji=c_i for the finite Lambert target, or C=I for the equally admissible singleton-block count. Its delta-residue is the required weighted hit sum. Primary: Caracciolo–Sokal–Sportiello, [arXiv:1105.6270](https://arxiv.org/pdf/1105.6270), Appendix A.5, Proposition A.14, gives the fermionic Gaussian determinant identity. Here the displayed finite coefficient/product identity avoids ALL factorial divisions in characteristic p. The number of modes is d, not J+h or a constant rank.

2. **Rectangular supercharacter.** With X_j=T_j^{-1}, Y_i=-u_i and rectangle lambda=(h^J), the Berele–Regev factorization gives

    s_lambda(X/Y)=product_(j,i)(X_j+Y_i)
                 = P*product_j T_j^{-h}.          (1)

The multiplier is an acquired unit. This is a gl(J|h) supercharacter and a finite supersymmetric Schur polynomial, not a representation of dimension J+h that evaluates itself. Primary: Moens–Van der Jeugt, [A determinantal formula for supersymmetric Schur polynomials](https://www-igm.univ-mlv.fr/~fpsac/FPSAC02/ARTICLES/Moens.pdf), introduction equations (1.6)–(1.12), including the Berele–Regev factorization. Experiment A below acquires its actual determinant-entry map.

3. **Weighted nonbacktracking graph zeta.** Use the complete bipartite graph on row vertices j and clock vertices i; give arc j→i weight T_j and i→j weight u_i. The reversal-pair determinant is exactly 1-w_ji. Weighted Bass reduction places their product P in an exact graph-zeta determinant identity. Primary: Ishikawa–Morita, [On the Ihara expression for the generalized weighted zeta function](https://arxiv.org/html/2210.13262), §3, derives finite edge-to-vertex determinant reduction with specified inverse arcs. Experiment B below proves the needed specialization directly, so no analytic infinite cycle product is specialized modulo N.

4. **Finite dual-Cauchy / exclusion-state sum.** Exterior Cauchy expansion gives

    P=sum_(lambda contained in h^J)
          (-1)^|lambda| s_lambda(T) s_(lambda')(u).

This is also a free-fermion transfer partition function with partition-valued boundary states. Primary: Naprienko, [Free Fermionic Schur Functions, arXiv:2301.12110](https://arxiv.org/abs/2301.12110), gives free-fermionic/supersymmetric Cauchy identities and refined Yang–Baxter structure; the displayed ordinary dual-Cauchy specialization is a finite polynomial identity. Summing all partitions or taking a fixed-height transfer state is not free: the number of shapes in the rectangle is binomial(J+h,J). This is a charge for that explicit expansion, not a lower bound for an integrable contraction. Schur/Cauchy precedent in the earlier string-theory packets retains credit.

The fermionic formulation also explains why small tensor description is not small matrix rank: its mass operator is I-diag(T) tensor diag(u). It has two operator-Schmidt terms on the tensor product but acts on d modes. Replacing it by I-a b^t computes 1-b^t a, a different finite polynomial. A low-rank Gaussian/Hubbard–Stratonovich substitution needs an actual identity retaining the extra induced couplings; outer-product edge weights alone do not authorize that replacement.

## 2. Experiment A: execute the small supercharacter determinant

Consider the interesting regime h>=J; if h<J, the full degree-h clock polynomial can already be emitted in soft(J+h), so no long-input compression is needed for this entry construction. The supersymmetric complete-function generating series is

    H(z)=sum_k h_k(X/Y)z^k
        = product_i(1-u_i z)/product_j(1-T_j^{-1}z)
        = G(z)/D_X(z).

Here G(z)=(z;rho)_h has degree h and D_X has degree J and constant coefficient one. Jacobi–Trudi gives a J-by-J determinant with entries

    h_(h-r+s)(X/Y), 1<=r,s<=J.                  (2)

These entries need only a band of 2J-1 coefficients near degree h, not all shapes. That is a real dimension reduction.

Now perform the exact polynomial division over the native ring:

    G=D_X Q+R, deg R<J, deg Q<=h-J.

The leading coefficient of D_X is a product of the supplied unit roots, so this division is legal; monic scaling is explicit. Every coefficient index in (2) is at least h-J+1, STRICTLY above deg Q. Therefore ALL entries come from the proper rational part R/D_X. Once R is acquired, their shifted recurrence band can be acquired in soft J by modular powering/recurrence extension. No additional long polynomial quotient is needed.

But R is precisely G modulo D_X, the old clock/row remainder in a reciprocal-root convention. Acquiring it by the existing initialized engine costs soft(J+sqrt(Jh)). Emitting all h q-binomial coefficients and dividing gives the weaker soft(h+J) implementation. The row roots being native conic roots has not supplied the missing R through this determinant formula. The short determinant's subsequent structured evaluation cannot make its absent coefficients into inputs.

Collision semantics are exact: (1) preserves P up to a unit, including nonunits and zeros, but a character formula involving divided alternants may not invert a cross difference X_j-u_i at the native hit. The polynomial Jacobi–Trudi form avoids that inversion. Differentiating it for a block pole pair would still require the deformed remainder R(delta); this experiment supplies no unit-start shortcut at the collision. This is a precise entry-initialization failure of the strongest straightforward supercharacter contraction, not a general impossibility for characters or scalar readout.

## 3. Experiment B: execute weighted Bass reduction and its tensor core

Let directed arcs e have tail t(e), head h(e), inverse bar(e), and weight a_e. Define

    K_(e,v)=1_(h(e)=v), L_(v,e)=1_(t(e)=v)*a_e,
    Jrev_(e,f)=1_(f=bar(e))*a_f,
    B=K L-Jrev.

Thus B is the weighted nonbacktracking arc operator. For each reversal pair e=(j→i), bar(e)=(i→j),

    I+Jrev = [[1,u_i],[T_j,1]], det=1-w_ji.

Sylvester's finite determinant identity, first over a universal polynomial ring and then cleared, gives

    det(I-B)=P*det H,
    H=I-L(I+Jrev)^-1 K.                         (3)

The vertex matrix is completely explicit:

    H_jj=1+sum_i w_ji/(1-w_ji),
    H_ii=1+sum_j w_ji/(1-w_ji),
    H_(j,i)=-T_j/(1-w_ji), H_(i,j)=-u_i/(1-w_ji),

with no other off-diagonal same-side entries. Rational forms hold only on the unit locus; the cleared determinant relation is universal. At desired collisions the reversal inverses in H are not numerically licensed.

### The residue target is an actual vertex trace

To retain the additive regulator, change reverse-arc weight to u_i/(1+delta). Then

    det(I+Jrev(delta))=P(delta)/(1+delta)^d,
    P(delta)=product_(j,i)(1+delta-w_ji).

The left vertex diagonal becomes

    H_jj(delta)=1+sum_i w_ji/(1+delta-w_ji)
      =1-h+(1+delta)sum_i 1/(1+delta-w_ji).      (4)

Hence its simple delta-residue is EXACTLY the original row hit count; a canonical squared-tag-weighted trace gives the corresponding tag count. Restricting j to a singleton block gives a valid noncancelling weak pair. This is a concrete new graph-theoretic interface to the desired scalar, not merely a zeta analogy. One may use unweighted residues because the block consumer allows any unit amplitude; the exact Lambert c_i target is a separate diagonal insertion, not a free h-entry array.

Equation (4) also exposes initialization: acquiring that vertex diagonal IS the finite singular Cauchy sum. The smaller H does not supply its entries. Generic numerical inversion or a Schur complement at these poles would be unlicensed. A determinant of H can have poles cancelling the P zeros in (3); det(I-B) is therefore not claimed to be a coverage-safe replacement for P. The correction must be retained, including its Laurent residue. Neither a new additive zero of a graph determinant nor a cancellation of P supplies an original multiplicative leaf certificate.

### Exact tensor simplification of the nonbacktracking side

Order forward arcs by (j,i). Two nonbacktracking steps (j,i)→(k,l) require k!=j and l!=i and have weight u_i*T_k. Thus the forward block of B² is

    A_J tensor A_h,
    A_J=(11^t-I)diag(T), A_h=diag(u)(11^t-I).

Because the two arc orientations give a bipartite block matrix,

    det(I-B)=det(I-A_J tensor A_h).              (5)

This is an exact initialized symbolic reduction: each factor is a rank-one perturbation of a diagonal, with known roots T_j or geometric u_i. If F_+(z)=product_j(z+T_j), their characteristic polynomials are

    chi_J(z)=z F_+'(z)-(J-1)F_+(z),
    chi_h(z)=z F_clock,+'(z)-(h-1)F_clock,+(z).   (6)

These follow from the rank-one determinant lemma after clearing; no inverse z+T_j is specialized at a zero. Acquiring chi_J costs soft J. The other factor is an Euler transform of the degree-h clock polynomial, with the known q-binomial coefficient structure; emitting it costs soft h. Treating its descriptor as an acquired norm against chi_J would repeat the original missing joint scalar operation. Formula (5) still acts on Jh arc-pair states and (3)'s correction contains the original poles.

### Full executed cost and finite guards

For an explicit numerical vertex-matrix construction, generating all Cauchy cross entries costs O(Jh) storage/arithmetic, with nonunit branches needing classification. Structured actions using full row and clock arrays read J+h entries, and the left trace still needs its singular diagonal; a soft-K action is not supplied. The safe initialized completion of the pole pairs remains the old shared G,G' row engine and residue/flag consumer, cost soft(J+sqrt(Jh)), plus soft-K block aggregation. No generic determinant or tensor-rank complexity claim improves this bill.

The weighted Bass primary theorem is used only as context for the proven finite identity (3). No positivity, complex convergence, root-of-unity parameter, graph-size-independent Gaussian elimination or arbitrary-unit pivot is assumed. Actual multiplicative leaves retain the new two-coordinate decoder after localization; graph additive zeros do not inherit it.

## 4. What this pass genuinely supplies

The four finite forms retain the actual T_j, rho, finite endpoints and canonical marks. The executed small supercharacter determinant pinpoints its missing remainder. The executed graph reduction supplies a new explicit vertex-trace realization (4), a paired-edge correction (3), and a rank-one-tensor core (5)–(6). All three graph formulas retain the singular input rather than silently divide it away.

No actual soft-K contraction was found. A meaningful successor could exploit the PARTICULAR graph Cauchy trace or its tensor-core/correction jointly; invoking Bass, Berezin, Yang–Baxter or a character name without initializing those displayed quantities would not do so. This report is an exact rewrite-and-execute ledger, not a broad lower bound or a new factor exponent.
