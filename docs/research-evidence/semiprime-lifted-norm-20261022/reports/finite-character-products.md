# Finite character products: exact reversal and primary theta audit

22 October2026. No simultaneous soft-m evaluator for the assigned H values was obtained. There is an exact paid reduction from two palettes to one when the supplied public prime m is3 modulo4. The inspected finite q-Gauss identity and generalized eta identities do not acquire that remaining product at the original prepared scalar q. This report does not repeat the prior Kopp/cyclic-reciprocity audit or claim a new backend primitive.

Retain N=P Q, m odd public prime, gcd(N,m)=1, q=gamma^(m²) a unit with both local orders>16m², L=mK+t<=4m², and J=O(m) assigned unit targets y_j=gamma^E_j q^(−kappa_j). The already reviewed boundaries and sufficiency addendum reduce factoring to assigned values of

    H_e(X)=product_(r∈R_e) product_(0<=n<K)(X−q^(r+mn)),
    R_e={0} union {r:Legendre(r,m)=e}.

All exponents below have O(log N) bits. K=0 means H_e=1 and needs no evaluator.

## 1. Exact finite reversal: two palettes become one when m=3 mod4

Assume K>=1. Put T=mK, D=K(m+1)/2, epsilon=Legendre(−1,m), and

    S_e=sum_(r∈R_e,n<K)(r+mn)
       =K sum_(r∈R_e)r + |R_e|mK(K−1)/2.

Reflect an exponent i=r+mn to T−i. For r>0 this becomes (m−r)+m(K−1−n), and its palette sign is e*epsilon. The zero-residue chain {0,m,...,(K−1)m} instead becomes {m,2m,...,Km}. Hence, EXACTLY as polynomials over Z/N,

    (X−q^T) H_(e*epsilon)(X)
      =(X−1)(−1)^D q^(−S_e) X^D H_e(q^T/X).    (1)

Here X^D clears the displayed reciprocal powers; no original collision product has been divided out. The scalar coefficient follows from

    X^D H_e(q^T/X)
       =(-1)^D q^S_e product_(i∈palette)(X−q^(T−i)).

This checks the normalization, including its inverse q^(−S_e).

When m=3 mod4, epsilon=−1, so all minus values are acquired from the ONE plus polynomial at the transformed unit targets q^T/y_j, after the following paid screens. For a minus-assigned row, take gcd with N of y_j−1 and y_j−q^T. A proper gcd factors; a saturated value gives the original gamma annihilator with index kappa_j or kappa_j+T. Those indices are nonnegative and less than L+m, so E_j>m²(L+m) makes both gaps positive. The retained setup discharges this bound, as proved in the earlier independent review. At most one decoder call is needed.

If these differences are units, evaluate H_+(q^T/y_j) and use (1) to obtain H_−(y_j). Plus-assigned rows ask H_+ at y_j directly. All target transformations, q powers, S_+ acquisition, powers y_j^D, endpoints and inversions cost soft O(m+J). The transformed arguments stay units; they need not be reinterpreted as new native row descriptors. A nonunit reconstructed H value is localized through its ORIGINAL unmasked scalar row, using the already proved sufficiency addendum. No localization of the transformed H query is required.

Thus a simultaneous H_+ evaluator at at most J explicit unit arguments suffices in this branch. This is only a factor-of-two common-polynomial simplification: H_+ still has degree D~m², and no faster evaluator follows.

When m=1 mod4, (1) is a self-reciprocity relation separately for each palette, and does not exchange them. One can equivalently append the endpoint T to obtain a fully reciprocal root set, but this only gives ordinary reciprocal-polynomial compression by a constant factor. No choice of public m in a progression, new all-input prime-supply claim, or improved factoring exponent is inferred here.

## 2. Exact finite q-Gauss identities: what actually survives

Chan--Chan prove the polynomial identity (their equation2.4)

    sum_(j=0..2n) [2n choose j]_Q (-1)^(n−j) Q^((n−j)²)
       =(Q;Q²)_n.                                (2)

As a polynomial identity it is legitimate over arbitrary coefficient rings; one must compute Gaussian binomial coefficients as polynomials or check their denominator units before using factorial quotients. It is a consecutive-odd-exponent product, not the Legendre-selected exponent set in H_e.

Their cyclotomic Gauss simplification then specializes Q to a primitive(2n+1)-st root, using their equation3.1 to collapse q-binomial coefficients. That additional step is not valid for q=gamma^(m²): q^m−1 is a certified unit because m is smaller than either local order. In fact

    Phi_m(q)=(q^m−1)/(q−1)

is a unit as well. The root-of-unity specialization cannot be inserted merely because the public character has modulus m. The source's root variable and our scalar progression step are different inputs.

The same exact issue applies to q-Gauss/q-Lucas congruences modulo Phi_m(Q) or its powers. If A(Q)−B(Q)=Phi_m(Q)^s C(Q), evaluation at the native q leaves a UNIT multiplier Phi_m(q)^s. It gives no vanishing modular error unless C(q) itself is acquired or independently shown zero. A cyclotomic-polynomial congruence is therefore not an equality modulo the unknown semiprime in this setup. This is a precise transfer check for that formula, not a general complexity lower bound.

## 3. Generalized eta products and the missing finite specialization

For Q formal or complex |Q|<1, define the character-selected infinite products using q-Pochhammer factors. A finite H_e is their endpoint quotient:

    H_e(X)=X^D product_(r∈R_e)
      (X^(-1)Q^r;Q^m)_infinity
       /(X^(-1)Q^(r+mK);Q^m)_infinity,             (3)

after the infinite tails cancel formally. The left side is an actual finite polynomial; the separate infinite factors on the right are not acquired finite-ring units.

Frye--Garvan's generalized eta products collect the ±r residue pairs and give modular identities for products attached to even real Dirichlet characters. Their variables satisfy Q=exp(2pi i tau), Im tau>0, and their modular identities involve infinite products and rational q-prefactors. In addition, the native H query has a free X argument: the usual one-variable eta product specializes X, rather than providing all assigned native X values. Introducing an elliptic variable produces theta/Jacobi objects but still needs a finite-ring evaluation theorem.

There is an exact reason formal truncation does not directly define such an evaluation. For any nonzero finite ring R and unit q∈R, there is no R-algebra homomorphism R[[Q]]→R sending Q to q: the series1−q^(-1)Q is a formal unit but would map to0. Thus an infinite power-series identity cannot simply be evaluated at a finite-ring unit. This does not rule out a separately proved finite cancellation identity such as (1) or(2), or a carefully controlled analytic lift; it identifies the extra theorem needed.

Here no exact N-divisibility bound for an analytic/formal tail has been supplied. Modularity can prove identities of the infinite functions, but it does not on its own prove that replacing finite H_e by a truncated theta expansion leaves the same residue modulo N. A selected algebraic root or a complex approximation without that error/divisibility certificate is not a legitimate acquisition of the native value.

## 4. The remaining actual algorithmic task

The paid reversal (1) is the strongest new exact finite-ring cancellation found here. In the m=3 mod4 branch the remaining task is one fixed degree-D character-period product at J assigned unit arguments; otherwise it is the two original products. The inherited generic simultaneous product evaluation still costs soft O(J+sqrt(JL)), about m^(3/2) in the native regime. A one-point q-product or fixed-level modular identity must not hide J independent evaluations or a growing level m in its constants.

A successful further identity must give those actual finite values, or a sufficient factor-producing observable, with its variable-m construction, all J arguments, unit screens and exact error terms paid in soft m. The inspected primary formulas do not yet supply that evaluator. There is no claim that all possible theta, modular-unit, nonlinear or character-cancellation methods are excluded.

## Primary sources and retained pins

1. H.H.Chan and S.H.Chan, *An amazing identity of Gauss and Jenkins' lemma*, Bulletin of the Australian Mathematical Society108(2023),86--98, online8November2022, DOI10.1017/S0004972722001216. Equations2.4,3.1 and Theorem3.1 inspected. Publisher: https://doi.org/10.1017/S0004972722001216 ; complete primary-paper PDF retained from https://mrc.sdu.edu.cn/ziliao/87.pdf as chan-chan-gauss-jenkins.pdf, SHA256 999b2df86f840a5dd244d66e331feef3cbaaef6ceeeac3755503fbf942bbba9b.
2. Jie Frye and Frank Garvan, *Automatic Proof of Theta-Function Identities*, author-hosted paper, definitions1.4,1.10 and Section3. https://qseries.org/fgarvan/papers/auto-theta.pdf . Retained frye-garvan-auto-theta.pdf SHA256 d14f6a070696299945edcdd7ff543826224cbb1f310daefe1bfb6ea85bc89a58.
3. Ofir Gorodetsky, *q-Congruences, with applications to supercongruences and the cyclic sieving phenomenon*, arXiv:1805.01254v1, https://arxiv.org/abs/1805.01254v1 . Cyclotomic/q-integer congruence input contract, not a finite-semiprime equality. Retained gorodetsky-1805.01254v1.pdf SHA256 bc0abc27fbac75071fa16efdf1e12b58af45a856c77f604194a7c61ce0e26a27.

Read the old semiprime-input-dependent-20261015/reports/cyclic-reciprocity-audit.md before this investigation; Kopp cocycles are not claimed as a new lead. Only the allocated character_identities scratch directory was written. No repo edits, subagents, backend changes, or finite success campaign.
