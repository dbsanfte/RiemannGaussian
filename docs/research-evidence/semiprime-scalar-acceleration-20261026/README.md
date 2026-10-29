# Two pole coefficients and optimal row selection for the long query

26 October 2026. **The long query has a smaller sufficient output: two pole coefficients recover the unique collision without acquiring its long cofactor amplitude.** A separate native support theorem gives a soft-K algorithm for the cheapest covered row partition. Neither result improves the uniform acquisition bound yet: the retained bound is soft K^(5/4), and the target remains soft K.

These are reviewed paper derivations under the existing preparation and coverage contracts. They are not compiled Lean theorems or a completed sixth-rate bit-complexity proof.

## Two coefficients recover the collision

Use the [publicly selected cover](../semiprime-unique-weighted-20261026/unique-cover.md), which guarantees exactly one good row-clock collision in a correct bin. Its acquired row polynomial is D(X)=product_j(X-T_j), of degree J=O(K), and the clock has h=O(K^(3/2)) points q^i. Define

    F_m(delta)=[1,q,...,q^m](1/(D(X)+delta)),
    R_m=Res_delta F_m.

The brackets denote a divided difference. At the unique collision theta=q^I, finite partial fractions give

    R_m=1/product_(0<=l<=m,l!=I)(theta-q^l)  if m>=I,
    R_m=0                                 if m<I.

Therefore

    theta=q^(h-1)+R_(h-2)/R_(h-1).

The final denominator is nonzero in the good field. Actual norm checks and the short tag consumer handle recovery over the prepared composite ring. This replaces the output of the original packed query; it does not claim numerical equality with that query or with the physical row deformation.

The earlier scalar E recurrence multiplied each divided difference by a long product. The new output needs no such normalization. All components have at most simple delta poles, including components with multiple hits. See [sectioned-newton.md](sectioned-newton.md) for the finite derivation, supplied initialization and unit guards.

## A compact kernel formulation

Geometric Newton conversion gives an ordinary series C_delta with

    (D(L)+delta) C_delta=1 mod z^h,
    L=(1+z)S,  S f(z)=f(qz).

After taking the residue, D(L)c=0. At the good prime this kernel is exactly one-dimensional. With B(z)=sum_(m<h) q^(m(m-1)/2) z^m/(q;q)_m,

    c(z)=(-1)^I*z^I*B(z)/(q;q)_I mod z^h,
    theta=q^(h-1)+q^(h-2)*c_(h-2)/c_(h-1).

Only the last projective pair is required. D and L specify the operator in O(J) space; there is no need to emit an h-by-h matrix or a full resolvent. Acquiring a nonzero kernel pair is still the missing operation. A zero residue prefix before the unknown I does not supply a nonzero start. The [kernel handoff](pole-kernel-handoff.md) states this distinction explicitly.

The first two scalar Graeffe attempts retain nonzero cross-parity terms with certified unit coefficients. They therefore do not inherit the ordinary Bostan–Mori halving bound. The exact coupled generator is

    L = [[1,q*u],[1,q]] S_(q²),  u=z².

The [repeated-section calculation](coupled-section.md) preserves a cyclic bidiagonal generator at every dyadic level. After the Euler conjugation, the pole has only one active section, indexed by I modulo the section size. [Bostan–Mori](https://mathexp.eu/bostan/publications/BoMo21.pdf) supplies the fast constant-coefficient algorithm; extending its runtime bound to this q-shift problem requires a further algorithm and proof.

This yields a concrete conditional shortcut. Choose the smallest power of two b>=max(1,h/K), so b=O(sqrt K). If r=I mod b is acquired, keep only indices r+b*t. Their number is at most K. Constructing that clock polynomial and evaluating it at all J row roots then costs soft K by ordinary product trees and multipoint evaluation. A polylogarithmic covering list of phases also suffices. Acquiring this genuine phase information remains open; merely rescaling the clock does not provide it. The [coupled-section review](algebra-review.md) checks the finite carries, boundary condition and cost.

## Optimize the actual rows before querying

The completed native supports are laminar: any two are nested or disjoint. Along a primitive coefficient direction, both eligible domains and phase classes coarsen with the 3-adic content. Different high-content directions have disjoint domains; the other supports are singletons.

A dynamic program on this sparse family finds the exact minimum full-window mass S_opt in soft K. It retains actual row representatives, forbids incomplete child covers and keeps empty-window support metadata. Combined with the existing unequal-window evaluator, it costs soft(K+sqrt(S_opt)); testing all cheap bins first gives a soft-K branch whenever the correct bin has S_opt<=K².

For balanced bins, however, every all-colour partition from this catalogue using full-bin integer windows has S_opt=Omega(K^(5/2)). Better selection within that particular model cannot alone reach the desired exponent. This price does not constrain direct kernel acquisition, a different family or an arithmetic sparse-clock selector. See [native-thinning.md](native-thinning.md) and its [independent review](native-thinning-review.md).

## Other executed contractions and validation

The [integrable calculation](integrable-closure.md) gives an initialized Christoffel frontier and exact Hankel/Toda minors for E_n. Direct execution costs soft Jh. Condensation needs additional moments and encounters prescribed zero initial pivots. A paid native screen also factors or certifies that D(X) and D(qX) have unit resultant, resolving this particular adjacent-shift cancellation attempt.

The [algebra review](algebra-review.md) checks signs, endpoint cases and division guards. The [standard-library checker](check_scalar_reductions.py) passes 231 exact checks of Newton conversion, the operator equation, first/interior/last pole locators, repeated nonhit roots, both Graeffe coefficients and Hankel identities. These check algebra, not native coverage or scaling. Reproduce with:

    python3 docs/research-evidence/semiprime-scalar-acceleration-20261026/check_scalar_reductions.py --output /tmp/scalar-reduction-replay.json

The next required result is an acquisition algorithm for the final pole or kernel pair in soft K, including its singular selection and composite-ring operations. The reduced output and optimal support selection are available; that runtime bound remains open.
