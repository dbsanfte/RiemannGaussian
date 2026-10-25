# Native shared twist: special-power closure tests

22 October 2026. Scratch research, no repository edits/build/coverage campaign. Read the current AGENTS tail (197 frozen entries), the dyadic-shared README, weighted-log-directions/additive-contraction/resampled-displacement/phase-direction-ledger, and the varying-weight-diagonal report. The paid norm/tangent constructor and first fused fold are inherited; they are not new results of this pass.

**No soft-O(m) all-H algorithm or original collision-support aggregate was obtained.** This pass derives two exact restrictions on proposed low-dimensional closures for the actual special unit B=W^N, and a characteristic-N wrap calculation. These are specific representation statements, not a general lower bound or factoring-rate result.

## Contract retained

Work over K=Z/NZ, A=K[X]/(X^m−1), m a power of two, with all prepared denominators and m units. Put

    W=t(1+gamma X)/(X+gamma), R=W/X, B=W^N,
    u=N^(-1) mod m,
    H_a=CT[rho_(u a)(B) R^a].

The actual integer power a is retained; the automorphism index alone is reduced modulo m. W and hence B are units. On retained nondegenerate components t and gamma^2−1 are units. One supplied tangent direction U and monomial shift remain paid; no moving direction is implicitly supplied.

## 1. Exact full rank of the translation closure, even for B=W^N

A proposed shared recurrence could keep a small fixed vector space/submodule V containing B and invariant under coefficient translations and odd coefficient dilations. The actual source rules out this particular approach outright.

Multiplication by B is an automorphism of the free K-module A. Therefore

    B, X B, X^2 B, ..., X^(m−1) B

is a K-basis of A: its matrix is the invertible cyclic multiplication matrix of B. Any submodule containing B and invariant under X multiplication must equal A. More generally invariance under one odd translation X^v suffices, since v is invertible modulo m and its powers run through all translations.

The transformed directions in the inherited skew-affine recurrence include exactly such coefficient translations: B_j -> B_(j−v). Thus a bounded-dimensional translation-invariant closure containing the actual B cannot be the missing algorithm; it must have full rank m. This strengthens the previous generic observation that the orbit could be large: here it is exactly full rank because B is a unit, with no genericity hypothesis or experiment.

This does NOT imply an m^2 lower bound for the desired contraction. The entire basis has the compressed representation “multiply by the one supplied unit B,” and cyclic convolution applies that operator near-linearly. What remains possible is a fast algorithm exploiting that compressed operator together with the varying row resamplings. Merely counting basis dimension does not settle that algorithmic question. The missing operation is still their joint twisted diagonal, rather than formation of the translation operator alone.

## 2. A Möbius-family shortcut cannot absorb interior automorphisms

Test the hoped-for closure

    W(X^a)=M_a(W(X)) in A,

with M_a another scalar Möbius transformation. Since W itself is invertible as a fractional linear transformation on retained components, this would express X^a as a Möbius function of X.

For 2<=a<=m−2, suppose

    X^a=(alpha X+beta)/(c X+d),

with denominator a unit in A and alpha*d−beta*c a unit. Then

    c X^(a+1)+d X^a−alpha X−beta = 0 in A.

Its degree is at most m−1 and its four exponents are distinct. Freeness of A forces all four coefficients to be zero, contradicting invertibility of the Möbius determinant. Thus this representation is impossible for every such interior a. The two edge actions a=1 and a=m−1 are the familiar X and X^(-1); reciprocal symmetry can relate those but cannot close all odd a.

There is a stronger bounded-degree version. If X^a=P(X)/Q(X), with deg P,deg Q<=d, Q a cyclic unit, and

    d < a,  a+d < m,

then Q X^a−P has degree<m and disjoint low/high coefficient intervals. It cannot vanish unless P=Q=0. Consequently any such rational representation must have

    d >= min(a,m−a).

For middle odd a this is Omega(m). Conjugating by W preserves rational degree, so the same obstruction applies to representing W(X^a) as a scalar rational function of W(X) of uniformly bounded degree.

This rules out a constant-degree PGL2/rational-symmetry closure, not sparse monomial evaluation. The paid shifted-norm constructor already handles high ordinary degrees caused by monomial shifts; the degree statement must not be misread as a complexity lower bound against that sparsity or against a different shared algorithm.

## 3. Characteristic-N differentiation: a legitimate parameter identity and an exact wrap ledger

Treat t and gamma first as formal parameters, localizing at the prepared unit denominators. The modulus X^m−1 is independent of gamma. Therefore parameter differentiation DOES descend to A, and

    partial_gamma B = partial_gamma(W^N) = 0 in A.

The same holds after a native relation gamma=t^2 is imposed by the chain rule: both the direct t derivative of t^N and the gamma contribution vanish. This legitimate identity differs from differentiating the reduced representative in X, which does not commute with cyclic reduction.

Unfortunately a zero parameter derivative does not force a scalar coefficient to be constant in characteristic N. Modulo a hidden prime P, the differential constants contain gamma^P, and the actual local expression is

    B(X) = W(X^P)^Q  (mod P), N=P Q.

Thus the identity retains the unknown-cofactor dependence, rather than producing a bounded-order scalar recurrence for H_a.

Here is the X-wrap issue explicitly for the special source. Let c_j be the ordinary Taylor coefficients at X=0 of W(X)^N, before cyclic reduction. Its logarithmic derivative gives the exact cleared three-term recurrence

    gamma(j+1)c_(j+1)
      = [N(gamma^2−1)−j(1+gamma^2)]c_j
        −gamma(j−1)c_(j−1),       c_(-1)=0.

It is a genuine constant-width hypergeometric/Jacobi-type coefficient relation before reduction. In K the N term vanishes. For 0<j<min(P,Q), the relevant integer denominators are units, and c_j=0, as already known from the formal Frobenius gap. This does not say the cyclic coefficients B_j vanish.

To make the alias accounting rigorous, work temporarily in the formal Laurent completion at gamma^(-1)=0. For each fixed N, the c_j tend to zero in this completion as j tends to infinity, so periodization is defined and equals cyclic rational reduction:

    B_k = sum_(r>=0) c_(k+r m),  0<=k<m.

Since the ordinary derivative is zero in K, every coefficient obeys j c_j=0. Define the convergent first wrap moment

    L_k = sum_(r>=0) r c_(k+r m).

Then exactly

    k B_k + m L_k = 0,
    L_k = −(k/m) B_k.

The factors r*m are essential. Replacing ordinary indices k+r*m by their residues k erases the entire wrap moment and incorrectly forces k B_k=0. Keeping the wrap terms makes the periodized derivative identity tautological rather than giving an additional recurrence for B. This identifies the precise cancellation in the tempting characteristic-N shortcut; it is not merely a warning that a derivative might fail.

The identities are rational in the parameters and therefore specialize on components where their denominators are units. The Laurent completion is used only to justify the periodization calculation, not as an algorithm that sums an infinite series at a numerical parameter.

## 4. Krawtchouk/q-hypergeometric check

Primary source inspected: Chihara–Stanton, [Zeros of generalized Krawtchouk polynomials](https://www-users.cse.umn.edu/~stant001/PAPERS/krlaur.pdf), pp.2–3, equations(2.1)–(2.8). It supplies the finite binomial generating function, three-term recurrence, and self-duality with its binomial weights. Also inspected Feinsilver–Schott, [Krawtchouk transforms and convolutions](https://link.springer.com/article/10.1007/s13373-018-0132-2), Sections3 and5, and Genest et al., [q-Rotations and Krawtchouk polynomials](https://arxiv.org/abs/1408.5292), primary abstract/model. No quoted passages are used.

The relevant ordinary generating factors indeed match the rational-power family after scaling: W^N=t^N gamma^(-N)(1+gamma X)^N(1+X/gamma)^(-N). The cleared recurrence above is therefore the appropriate usable identity. Standard finite-dimensional orthogonality/self-duality additionally assumes its specific additive coefficient range and binomial measure. Our contraction replaces that index by u*a*k modulo m and includes all cyclic wraps. The source identities do not identify that resampled measure with the original one.

In particular hypergeometric expressions containing a denominator Pochhammer (−N)_j cannot be divided through in K: its first factor is already zero. Cleared polynomial/binomial identities may remain valid, but they cannot justify those inverses or eliminate aliases.

For q=X^u on a primitive spatial component the actual summand ratio remains

    T_(a+1)/T_a
      = R(X) * [(1+gamma q z)(z+gamma)
                /((1+gamma z)(q z+gamma))]^N,
      z=q^a.

Calling this degree-two q-hypergeometric data would drop the Nth power. Before cyclic reduction its rational coefficient has degree2N; after reduction one can encode it using acquired degree<m coefficient lists for one q. That reduction retains the original phase dependence and is not one scalar recurrence simultaneously for all X roots. Standard q-Krawtchouk matrix identities also require checking all q-Pochhammer denominators on every retained cyclotomic stratum; roots of unity do not make those factors automatically invertible. No bounded-order, all-phase recurrence or shared near-linear preprocessing follows from the inspected identities.

## 5. Why a scalar CT aggregate has not replaced localization

A computed sum of H_a, even if obtained near-linearly, is a linear contraction of source values. The sufficient original query is a product of original differences over a supplied row subset and seed interval, with restriction-stable same-leaf support and recovery. There is no supplied implication from vanishing/nonvanishing of a CT sum to vanishing of one such original difference on the same hidden-prime leaf.

The elementary fact that a unit such as X has CT zero already shows why trace vanishing alone is not a zero-divisor certificate. This example is not claimed to be an actual native collision instance; it isolates the missing algebraic implication. A proposed aggregate must prove a source-specific support theorem and restriction/localization rule, rather than promote linear trace cancellation into a collision. The native ell_j powers and common long seed index also remain in that theorem's scope.

## Cost and next constructive obligation

All acquired data in this pass are identities about the already-paid O(m)-coefficient B and rational W. Testing one actual H_a still costs soft O(m) by cyclic automorphism, powering and CT, and applying that independently to m outputs gives soft O(m^2). The paid norm/tangent primitive computes one fixed weight's full power sequence in soft O(m), but the identities above do not convert the moving weights into such a fixed family. No new total soft-m acquisition is claimed.

A useful remaining route must bypass the impossible small translation-invariant linear state and constant-degree Möbius closure, while retaining compressed convolution and affine resampling together. A concrete sufficient result would factor the twisted coefficient operator

    B -> (CT[rho_(u a)(B) R^a])_a

on this special B using shared sparse/tangent operations whose total scalar input/support measure is soft O(m), or produce a different restriction-stable original-difference query with that cost. Neither has been constructed here. No generic lower bound is asserted; the target factorization exponent remains unproved.
