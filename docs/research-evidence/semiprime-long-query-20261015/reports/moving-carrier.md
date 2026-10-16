# Source structure and moving numerical-q carriers

2026-10-15. Scoped algebraic analysis; no near-linear acquisition and no general scalar lower bound.

## Source pins

Restored and SHA256-verified archive originals:
- antipodal-trace-candidate.md: a67c02ed0746321c59dd18f8484918711e77b114e7e15c8ed6954fae0cbdd54a
- inverse-indexed-normalized-current-candidate.md: af98fbc1bf39a1d2a617d1294a80621377345d3f4e52e01dfa2ea282cd87f17a
Archive: /home/dbsanfte/riemann/formal/docs/research-evidence/research-checkpoint-20261012/index.json.
This analysis uses their stated actual-source identities, not a new verification of every upstream lift.

## What numerical squaring actually asks for

Write P_L(X)=prod_{0<=i<L}(X-u q^i). Then
P_{2L}(X)=P_L(X) q^{L^2} P_L(q^{-L}X).
For odd length multiply the additional endpoint X-u q^{2L}. All inversions here are of known units.

If only P_L modulo H is retained, substitution into the second factor is not a well-defined operation on R[X]/H unless H(q^{-L}X) is a unit multiple of H(X). The correct second residue is acquired in a different quotient: one must know P_L modulo the monic polynomial q^{-LJ}H(q^{L}X) before substituting. Indeed a discarded multiple H(q^{L}X) becomes a multiple of H(X) after X is replaced by q^{-L}X. The original ideal (H) is not generally preserved by that substitution. This is an exact dependency, not a running-time lower bound. A moving quotient implementation is permitted; its acquisition cost must be counted.

Equivalently, evaluating P_L at all roots Y_j needs evaluation at q^{-L}Y_j for the second child. After k expansions, the required target sets are translates q^{-s}Y_j. Separate translated residues can be consolidated by a product/remainder tree, but constructing the explicit union carrier costs its degree. Symbolic compression might avoid that cost and remains outside this observation.

For variable L_j, apply this identity rowwise, retaining each odd endpoint. Grouping by length does not make the starting origins equal.

## Actual inverse-indexed structure

The normalized source has x_j=gamma^{r_j}, v_j=gamma^{a_j}, alpha=gamma^{m^2}, with r_j=-2N/j (mod m), a_j=N/j^2 (mod m), and -m^2<r_j<1.5m^2. Its quadratic constraint r_j^2=4Na_j (mod m^2) is a relation between integer exponents. It is not a polynomial relation x_j^2=v_j^{4N}: the latter would require 2r_j=4Na_j modulo ord(gamma), an unrelated assertion.

A precise small monomial check is available. Suppose, for at least three distinct nonzero tags, x_j^A v_j^B alpha^D=gamma^C, and suppose all exponent differences A r_j+B a_j+D m^2-C have absolute value smaller than the actual gamma order. Equality therefore forces those differences to vanish in Z. Reducing modulo prime m and multiplying by j^2 gives
C j^2+2AN j-BN=0 (mod m).
A quadratic with at least three roots is zero, so A=B=C=0 (mod m), since N is coprime to m. Thus |A|,|B|<m forces A=B=0. In that range any such relation is scalar only. The size assumption must be checked for the actual chosen order; it is not automatic for arbitrary D or C. This excludes a small monomial parametrization of the two coordinates, not sparse multi-term equations or nonlinear algorithms.

## No accidental free shared carrier from normalization

For normalized targets, gamma^{r_j+m^2 s}=gamma^{r_k+m^2 t} with exponent difference strictly smaller than ord_N(gamma) implies r_j-r_k+m^2(s-t)=0. Modulo m this forces j=k; then s=t. The preserved global distinct-period supply ord_N(gamma)>m^{4.062} makes this applicable to 0<=s,t<O(m^2), where the exponent range is O(m^4). Thus the literal product with one linear factor for every translated normalized node has degree J times the number of shifts, and distinctness permits no deduplication of its linear factors. This is NOT a lower bound for an arbitrary monic polynomial vanishing at those nodes: over a composite ring a degree-d monic polynomial can have more than d distinct roots (for example X^2-1 modulo 15 has four). Distinctness modulo N does not imply their pairwise differences are units: this statement does NOT invoke a CRT decomposition or a local-field rank lower bound. Nor does it lower-bound implicit representations or a single resultant.

The actual normalized baby origin also depends on the slope via gamma^{-N-a_j}alpha^{-floor(e_j/2)}. Replacing it by a common origin discards the a_j digit and is not source preserving. Antipodal trace folding retains this dependency.

## Outcome

Numerical base squaring is valid, but fixed-degree quotient reuse requires acquiring translated quotient residues. The actual inverse-indexed source prevents a trivial bounded-monomial elimination and free identification of those translated normalized targets in the stated global-order range. No proof here rules out a compressed scalar cocycle, a genuinely implicit moving carrier, or a near-linear source-specific evaluator. Those are still the missing acquisition theorem.

## Strengthening: actual fixed-carrier failure at every short nonzero shift

Over either hidden field assume the actual order of q is a prime R>J, and 0<s<R. Let H be monic of positive degree J with H(0) nonzero. If H divides H(q^s X), degree comparison forces H(q^s X)=q^{sJ}H(X). Comparing constant terms gives q^{sJ}=1, hence R divides sJ, impossible because R is prime, 0<s<R and 0<J<R. Therefore scaling cannot descend to the fixed quotient at any such s. The same argument applies to negative shifts by reducing them modulo R. In the supplied hard family L=O(m^2)<R>m^{2.031}, every nonzero doubling shift up to L satisfies this condition eventually. This strengthens the generic quotient warning to the actual family, conditional only on the supplied order and degree hypotheses. It remains an obstruction to this fixed-residue interface, not to richer representations.
