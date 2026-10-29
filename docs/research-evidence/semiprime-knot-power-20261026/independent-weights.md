# Independent Alexander weights: a legal diagonal torus, no new contraction

26 October 2026. Corrected after independent review. Garoufalidis–Kashaev Section 7.2 equation (101) states a two-independent-argument Alexander product on a four-dimensional Nichols model, but its summary table marks the same equality with a question mark. Independently, at the ordinary exterior point p=1 a normalized tensor construction proves arbitrary-many independent Alexander factors, and a rank-m diagonal twisted-Alexander representation gives an exact determinant. My earlier claim extending independent KM scalings through generic p omitted the separate braided-category naturality condition and is withdrawn: native distinct weights violate that condition when p is arithmetic q. None of the valid constructions supplies the desired soft(L+sqrt(m)) contraction.

## 0. Published two-weight formula, source inconsistency and conjecture boundary

Primary: Stavros Garoufalidis and Rinat Kashaev, *Multivariable knot polynomials from braided Hopf algebras with automorphisms*, Publications RIMS 62 (2026), 75–114, DOI https://doi.org/10.4171/PRIMS/62-1-3, published PDF https://ems.press/content/serial-article-files/52259?nt=1; inspected arXiv text https://arxiv.org/html/2311.11528, Sections 7.1–7.2. At auxiliary omega=1, its Nichols f-algebra has dimension four and the paper explicitly states

    Lambda_(1,K)(t_1,t_2)=Delta_K(t_1)Delta_K(t_2).       (0)

This is equation (101), with canonically normalized Alexander polynomials. Definition 7.1 defines Lambda as the (1,1)-entry of the long-knot endomorphism in its stated Nichols basis; the invariant is Laurent-polynomial in the two independent units. Section 7.2 states the omega=1 formula without qualification, while Table 2 on printed p.110 of the PUBLISHED PDF puts a question mark above this SAME product equality (the arXiv table does too). Section 7.1 Conjecture 7.2 separately asserts that the general endomorphism is Lambda times identity. We therefore record the published formula and its inconsistency, rather than claiming a fully proved theorem identifying all GK normalization choices. Equation (124b) also explicitly defers its proof to a subsequent publication. The independent p=1 tensor argument below supplies a separate proof for our chosen ordinary exterior model, not an identification of every GK model or its generic parameters.

Thus the literal four-state invariant has two genuinely independent parameters, and the stated formula would specialize to two desired odd-argument factors. The independently normalized tensor model below establishes that two-factor product without relying on the publication's conflicting status labels. Pairing repeatedly still leaves m factors or an exponentially growing tensor state; neither (0) nor this tensor proof supplies bounded-state fusion of the entire geometric alphabet.

## 1. Diagonal scaling: simultaneous covariance is insufficient at generic p

Primary source: Kashaev–Mangazeev, *On braided Hopf structures on exterior algebras*, https://arxiv.org/html/2505.15569v1, equations (26),(27), Section 5 equations (34)–(36), and Section 5.1. The paper explicitly chooses phi_t(f_E)=t^|E|. The following extension is our direct verification, not a quoted additional theorem of that paper.

For a basis e_1,...,e_m of V and independent units t_1,...,t_m, define

    phi_T(f_E)=(product_(i in E)t_i) f_E.                (1)

For m=2 its matrix on (1,e_1,e_2,e_1 e_2) is exactly

    diag(1,t_1,t_2,t_1 t_2).

The exterior multiplication and the braided coproduct preserve each basis color's total multiplicity. The coproduct is induced from primitive generators in the braided tensor algebra and its multihomogeneous exterior ideal. In the paper's explicit exchange channel,

    E'=(E\G) union H, F'=(F\H) union G,

so for every color i,

    1_(i in E)+1_(i in F)=1_(i in E')+1_(i in F').

Consequently phi_T is a linear algebra/coalgebra automorphism, preserves unit/counit and antipode, and satisfies the simultaneous covariance identity

    (phi_T tensor phi_T) tau_hat
          =tau_hat (phi_T tensor phi_T).                (2)

This does NOT suffice to make phi_T an allowed morphism in the ambient braided category. Garoufalidis–Kashaev Remark 3.1 and Definition 3.2 require the automorphism to be an ambient-category morphism. Naturality separately requires

    tau(phi_T tensor Id)=(Id tensor phi_T)tau,
    tau(Id tensor phi_T)=(phi_T tensor Id)tau.            (2a)

These are stronger than (2). In the KM generator convention

    tau(e_2 tensor e_1)=(p-1)e_2 tensor e_1-e_1 tensor e_2,

the coefficient of e_2 tensor e_1 in the first identity (2a) gives the NECESSARY condition

    (p-1)(t_2-t_1)=0.                                 (2b)

Likewise every nonzero color-exchange channel imposes the corresponding equality of weights, up to annihilation by its coefficient. Over a field with p!=1 this forces t_1=t_2. Over a composite ring one must use the displayed annihilator condition, not assume cancellation by p-1. For the native short distinct geometric weights t_1,t_2, their difference is a unit under the actual local-order guard, so (2b) forces p=1. Taking p=arithmetic q!=1 is therefore invalid for this independent-weight application.

My earlier inference from multidegree conservation to an admissible generic-p Hopf f-object was incorrect. Substituting that linear map into formulas (35),(36) still gives a polynomial operator, but the cited construction does not prove its Yang–Baxter identity. No generic-p independent Cartan family is established by this calculation. At p=1 the mixed channel vanishes and separate naturality holds for independent scalings; that valid case is used below.

This correction does not invalidate GK's actual rank-two diagonal-type Nichols construction: its generator braiding is tau(x_i tensor x_j)=q_ij*x_j tensor x_i, with no same-order Hecke exchange term. Independent diagonal scaling slides separately through that braiding and is explicitly part of their Section 7.1. It is a different braided input from the generic-p KM exterior model; conflating them caused the invalid extrapolation.

## 2. Separate the R-matrix from scalar knot normalization

The generalized Yetter–Drinfeld theorem gives a Yang–Baxter operator only after its full ambient-morphism hypotheses are met. The proposed generic-p independent scaling fails that prerequisite, before questions of scalarity, modified trace, or higher-rank Links–Gould identification arise. No such generic-p braid representation or product formula is claimed here.

There is, however, a completely controlled specialization. Set the auxiliary deformation p=1. The braided Hopf algebra is the ordinary super exterior algebra, with

    Lambda(V)=tensor_(i=1)^m Lambda(F e_i)

as a braided Hopf tensor product. Equation (1) is the tensor product of independent one-mode automorphisms. Reordering graded tensor factors therefore factors the full tangle construction into its m two-dimensional Alexander models. Use the one-mode reciprocal normalization K(1)=1 given in Section 5.1, where the reduced knot endomorphism is K(t_i) times the identity. Tensoring these already normalized tangle maps proves

    J_T(K)=product_(i=1)^m K(t_i) * Id_(2^m).             (3)

For two modes the state rank is 4 and the scalar is K(t_1)K(t_2), with genuinely independent t_1,t_2. For m modes the explicit state rank is 2^m. This normalization proof uses factorization at p=1; it does not extrapolate a modified-dimension quotient through a singular generic-p specialization.

The auxiliary p=1 has no relation to setting arithmetic q or eta to a root of unity. The desired specialization is t_i=eta^(2i+1) in the supplied composite ring.

## 3. A known determinant with independent Cartan eigenvalues

A second concrete realization uses the abelian representation of the knot group

    alpha_D(g)=D^lk(g), D=diag(t_1,...,t_m).

Its rank is m, not 2^m, and its meridian eigenvalues are independently chosen. Primary source: Boden–Friedl, *Metabelian SL(n,C) representations of knot groups IV: twisted Alexander polynomials*, https://arxiv.org/abs/1209.4244 and author/institute fulltext https://pure.mpg.de/pubman/item/item_3120919_3/component/file_3120921/Boden_Metabelian_oa_2014.pdf, Section 1.1 and Lemma 5. Direct sums multiply twisted Alexander invariants; a one-dimensional meridian value z shifts the Alexander variable to tz and introduces denominator 1-tz. These are direct-sum facts, not an assertion that general tensor-product twisted invariants multiply.

Thus, over the generic Laurent ring, multiplying the twisted torsion by det(I-uD) gives the normalized product product_i K(u t_i), up to the usual unit normalization fixed by the chosen reciprocal K. One should not evaluate the rational torsion first at a composite-ring singularity and then divide. The following division-free determinant fixes the normalization directly.

If the acquired Seifert matrix V has size 2L and convention

    K(t)=t^-L det(t V-V^T),

then exact block decomposition gives

    product_i K(t_i)
       =det(D)^-L det(V tensor D-V^T tensor I_m).        (4)

The determinant has order 2Lm; its extra normalization det(D)^-L is a known unit. Equation (4) is valid over every commutative coefficient ring, including R=Z/NZ and collisions. It supplies a genuine higher-rank torus restriction with independent eigenvalues and a known determinant, without a supergroup conjecture.

## 4. Native singular arithmetic and acquisition ledger

At p=1 the individual two-state Alexander matrices involve unit t_i and polynomial factors such as 1-t_i. The latter need not be inverted. Use the already integral reciprocal Alexander scalar or the Seifert determinant (4), so zeros and zero divisors K(t_i) remain valid outputs. A generic-field typical-module decomposition or Wada torsion denominator is not automatically a legal modular inverse.

Choosing t_i=eta^(2i+1) gives exactly the native odd-weight product. A symbolic descriptor (eta,m) is short, but explicitly acquiring all diagonal eigenvalues still costs m scalar writes. The full exterior state space costs 2^m basis coordinates; the determinant in (4) costs 2Lm dimensions and O(Lm) nonzero entries even for the sparse acquired V. An implicit tensor/Kronecker description avoids those writes but does not supply its determinant.

The initialized scalar completion remains the existing geometric product algorithm, soft(L+sqrt(Lm)), or explicit O(Lm) evaluations. No theorem inspected here contracts (3) or (4) in soft(L+sqrt(m)). In particular, the rank-m diagonal representation is not an acquired constant-rank object, and its independent eigenvalues are not equal-argument tensor powers that can be evaluated by binary exponentiation.

The useful positive objects remaining after correction are the p=1 independent-weight exterior scalar, with separate naturality and a tensor normalization proof, and the rank-m diagonal twisted determinant (4). Generic-p total-multidegree covariance is not an additional valid braid construction. A genuinely useful further theorem would evaluate that implicit determinant for geometric D in the desired additive cost. Its existence is not implied by the p=1 Cartan construction itself.

No repository files, source reports, or numerical tests were changed or used. This is an independent-weight construction/audit, not a broad survey or a new factoring bound.
