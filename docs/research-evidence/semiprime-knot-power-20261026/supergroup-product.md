# Supergroup Alexander products: exact factorization, acquisition still unpaid

26 October 2026. Bounded primary-literature audit; no experiments or repository edits.

**Outcome.** There is a proved Alexander PRODUCT specialization of every Links–Gould invariant LG^{n,1}, but it is the power K(t)^n with one common argument. The distinct odd-argument product is obtained exactly by independent tensor factors of the Alexander model; executing that factorization gives the existing scalar geometric-product problem, rather than a new fast evaluation. The new unrolled colored sl(2|1) family does not supply the missing independent arguments: its Alexander specialization is K(t)^2 independent of color. No soft O(L+sqrt(m)) scalar algorithm is established here.

## 1. Two different root specializations, with exact scope

**Published theorem, De Wit–Ishii–Links, Theorems 4.2–4.3 (2005):** for an oriented link and an integer r coprime to n,

    LG^{n,1}(L; tau, exp(pi*i*r/n)) = Delta_L(tau^(2n)).

This collapses the rank-2^n representation to ONE Alexander evaluation. It does not produce a norm over its shifted weights. This auxiliary quantum root is not the arithmetic eta, which has large odd local order. Evaluating the right side directly is legitimate, without constructing an auxiliary cyclotomic ring or the representation; it costs soft O(L+log n) once K's coefficients are acquired. Choosing tau cannot turn a single evaluation K(tau^(2n)) into the prescribed product for arbitrary K.

**Published theorem, Kohli–Patureau-Mirand, Theorem 4.1 (2017):**

    LG^{n,1}(L; tau, -1) = Delta_L(tau^2)^n.

Their Proposition 4.2 gives the precise reason the arguments coincide. The specialized 2^n-dimensional module V_{-1}(0^n,alpha) is the tensor product of n two-dimensional Alexander modules, ALL isomorphic to V_a, with a=q_aux^(-alpha)=tau. In the proof each k_i^2 acts by the same scalar a^2. Propositions 4.3–4.4 identify pivotal operators and braiding conjugations, and the proof ends with the reduced partial-trace scalar d=c^n. There is no independently selectable a_i in this standard minimal LG family.

The distinction survives normalization: the theorem concerns the reduced link invariant, normalized on the unknot, not an ordinary quantum dimension that vanishes. For the native knot, choosing tau=s0^(2i+1), where s0^2=eta, yields K(eta^(2i+1))^n. The scalar algorithm evaluates this ONE K-value, then performs binary exponentiation, soft O(L+log n). Over the squarefree composite ring, its zero bit is that of this one K-value; it cannot aggregate the other odd arguments. The assertions here are polynomial-specialization uses of the theorem, not substitution into a generic modified-dimension quotient at a singular auxiliary root.

These two theorems are compatible when their auxiliary roots coincide; they are different specializations in general. Neither requires, or permits, replacing arithmetic eta by -1.

## 2. Execute the genuinely independent-argument product

There IS an exact product construction, with no conjectural supergroup identification required. Take m copies of the normalized two-dimensional Alexander tangle model, each with its own variable t_i, and take the tensor product of their braidings, cups, caps and reduced partial traces. Reorder tensor factors so all copies of each mode are adjacent. For a fixed knot tangle, the scalar endomorphisms multiply:

    J_tensor(K; t_1,...,t_m) = [product_i K(t_i)] I_(2^m).

This is a **derived tensor-product identity**, not a claim that the ordinary one-parameter LG^{m,1} module admits those independent weights. It is the same linear-algebra factorization used by Kohli–Patureau-Mirand, now without imposing equality of the mode parameters. Choose t_i=eta^(2i+1), so the scalar is exactly P_m. The half-powers required by conventional two-dimensional matrices are available as s0^(2i+1); reciprocal conventions t_i versus t_i^-1 give the same K.

Execute the scalar side instead of the 2^m-dimensional operator:

1. Acquire the already available degree-2L reciprocal K (or its sparse Seifert realization). There is no need to acquire a knot diagram, a generic LG invariant or any R-matrix tensor entries.
2. Set t_1=eta^3 and t_(i+1)=q*t_i with q=eta^2.
3. Compute P_m=product_(i=1)^m K(t_i), by division-free evaluation and multiplication, or by the existing geometric product algorithm.
4. Use its zero/nonunit bit with the existing prefix consumer.

Straight Horner evaluation costs O(Lm); explicitly producing all m samples costs at least m scalar writes. The currently paid compressed geometric-product implementation costs soft O(L+sqrt(Lm)); the factorization introduces no operation reducing that bound. Listing all independent weights costs O(m), although their arithmetic progression has an O(log m)-size symbolic descriptor. The latter descriptor does not supply the scalar contraction.

This construction is safe at collisions: it contains no division by K(t_i), and the identity is polynomial/Laurent-polynomial in unit t_i. One may therefore use the integral normalized Alexander scalar model or simply the division-free Seifert polynomial evaluation over R, even where P_m=0 or is a zero divisor. This does NOT extend every generic-field typical-module or modified-trace normalization across its poles. Explicit state rank is 2^m; rank-m determinant descriptions of the scalar still require their determinant/norm computation. Neither descriptor is an acquired fast scalar.

A precise potentially useful remaining primitive is consequently:

    Given normalized reciprocal K of degree 2L and the binary descriptor
    (eta,m), contract the independent Alexander-model tensor product
    at t_i=eta^(2i+1) without expanding the m modes, in soft O(L+sqrt m).

This is an exact initialized formulation, but algebraically is still the target norm. No result audited here gives that contraction. This is not a lower bound on other supergroup algorithms.

## 3. Why the apparent extra parameters do not currently fix acquisition

**Component variables.** Kohli–Patureau-Mirand Remark 4.5 discusses the Geer–Patureau-Mirand multivariable invariant M(L;q_aux,q_1,...,q_c), where c is the number of ordered LINK COMPONENTS. These are not n mode parameters on the same knot strand. Moreover the claimed extension M(L;-1,q_1,...,q_c)=ConwayPotential(q_1,...,q_c)^n is explicitly phrased as something to which their proof “should adapt,” rather than their proved Theorem 4.1. Its normalization relation contains product_(j=0)^(n-1)(q_aux^j/tau-tau/q_aux^j). One cannot divide that expression after a specialization unless all its factors have been certified units. Passing to an m-component cable would also require a cabling/satellite formula and its acquisition; it is not an already acquired product of the individual knot evaluations.

**Unrolled colored sl(2|1).** Garoufalidis–Harper–Kashaev–Kohli–Wagner, Theorem 1.3, prove

    LG^(n)(x,1)=Delta(x^2)^2

for every color n>=1; the representation dimension is 4n. Here x=q_aux^alpha is retained as an independent variable when q_aux is set to 1. This does not mean substituting an ordinary finite exponent alpha into 1^alpha. The color does not create the m distinct odd weights in the Alexander limit. Cabling Theorem 1.1 instead expresses parallel evaluations as a SUM with representation multiplicities and modified-dimension ratios; it is not the independent product above. Thus color n=m is not a compressed norm algorithm.

**2025 exterior-algebra formulation.** Kashaev–Mangazeev, Section 5, use the automorphism phi_t(f_E)=t^|E| f_E and a deformation parameter p. Their dim(V)=1 example is exactly J=Delta(t)I with reciprocal normalization Delta(1)=1. The proposed higher-dimensional identification with LG is conjectural in that paper, and the displayed automorphism has one common t, not independently prescribed t_i. It supplies explicit 2^m-state formulas, but no theorem acquiring the independent-weight scalar in sublinear m time. This makes the ordinary exterior-algebra independent-mode contraction a sensible place to seek a genuinely new structured algorithm; its existence is not inferred from that conjecture.

## 4. Source metadata

All links below are primary sources. Formula summaries above use their indicated theorem/section; results with different q conventions have deliberately been named q_aux.

* D. De Wit, A. Ishii, J. Links, *Infinitely many two-variable generalisations of the Alexander–Conway polynomial*, Algebraic & Geometric Topology 5 (2005), 405–418, published 22 May 2005, DOI 10.2140/agt.2005.5.405. Theorems 4.2–4.3; minimal-family rank and variables in introduction. https://msp.org/agt/2005/5-1/agt-v5-n1-p18-p.pdf ; preprint math/0405403, https://arxiv.org/abs/math/0405403 .
* B.-M. Kohli, B. Patureau-Mirand, *Other quantum relatives of the Alexander polynomial through the Links–Gould invariants*, Proceedings AMS 145 (2017), 5419–5433. Inspected arXiv:1606.02538v1, 8 June 2016; Theorem 4.1, Propositions 4.2–4.4, Remark 4.5. https://arxiv.org/abs/1606.02538 ; https://arxiv.org/html/1606.02538 . Inspected local PDF/text are fingerprinted in sources.json.
* S. Garoufalidis, M. Harper, R. Kashaev, B.-M. Kohli, E. Wagner, *On the colored Links–Gould polynomial*, arXiv:2509.10911 (2025); inspected author-hosted 27-page PDF, dated 10 September 2025, and independently checked arXiv v3, 17 December 2025. Theorems 1.1–1.3 are unchanged for this use. https://arxiv.org/html/2509.10911v3 ; https://guests.mpim-bonn.mpg.de/stavros/publications/colored-LG-polynomial.pdf .
* R. Kashaev, V. Mangazeev, *On braided Hopf structures on exterior algebras*, JPAA 229 (2025), 108135, DOI 10.1016/j.jpaa.2025.108135; inspected arXiv:2505.15569v1, 21 May 2025, Section 5 and abstract. https://arxiv.org/html/2505.15569v1 .

Priority recommendation: distinguish the independently parameterized Alexander tensor-product scalar contraction from ordinary LG rank/color specialization. The former encodes the desired product exactly and safely at zeros, but still needs a new scalar contraction primitive. The proved LG specializations evaluated through their Alexander right sides are cheap only for a single argument or repeated equal argument. This lead provides no exponent gain yet.
