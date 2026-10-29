# Long-query representations and the torus hybrid

26 October 2026. Three parallel Sol 6.1 investigations, independent cross-reviews, root derivations and exact structural experiments. **No uniform sixth-root acquisition theorem is claimed.** Two usable changes are incorporated into the research hybrid: a complete torus-only collision branch and a simpler value-only tagged readout. The current route's worst-case acquisition bound remains soft O(K^(5/4)), with K~N^(1/6).

## The query and the counting convention

The original coupled query is

    P=product_j product_(0<=i<h)(1-T_j*rho^i),
    J=Theta(K), h=O(K^(3/2)).

We do not need to output P. The frozen singleton blocks admit two short outputs carrying a squared colour; the newly complete torus decoder permits a different coverage-preserving query that needs only an actual nonliteral torus collision.

This pass catalogues **15 representations or readout interfaces across 10 mathematical domains**. This is an organizational count, not a claim that the domains are independent, that all forms are new, or that there are only finitely many possible rewrites. Several are exact identities for P; others preserve the needed zero support or provide a weaker sufficient statistic. Those distinctions are part of the ledger.

| Domain | Numbered forms in this pass | What it exposes; actual acquisition status |
|---|---|---|
| 1. Finite q-series | 1: P as a product of q-Pochhammer symbols; 2: finite Lambert partial fractions | Changes a clock sum into an inverse row product. Exact finite identity; long products remain. |
| 2. Approximation and orthogonal polynomials | 3: Padé/rational quadrature; 4: Askey–Wilson lowering | Cheap moments and explicit error, or a shifted difference. The native pole remains in the Padé error; lowering retains the long bulk. |
| 3. Elimination theory and local algebraic geometry | 5: Cauchy-transform/local residue; 6: norm/resultant in the public-label algebra | Gives a short modulus without requiring distinct numeric row roots. The composition G_h(Y) modulo that modulus is unpaid at target cost. |
| 4. Structured linear algebra | 7: companion weighted resolvent; 8: gated determinant/adjugate first coefficients | The new gated readout needs three coordinates per block and only row VALUES. No full matrix, clock derivative or Lambert normalization is needed for its downstream computation. |
| 5. Cyclic groups and arithmetic supports | 9: divisibility/annihilator support of torus exponents | Dropping the scalar coordinate permits untagged aliases, duplicate removal, sign folding and safe nonzero supercovers. Exact interval union has a computable adaptive bound. |
| 6. Discrete dynamics and symbolic recurrences | 10: common scalar order-two Lucas streams | All seeds and the common recurrence are acquired in soft O(K). A fast simultaneous zero query along their long common orbit remains open. |
| 7. Knot theory and character varieties | 11: SL2 trace/skein product-to-sum | The torus norm becomes a two-by-two trace identity. This is the classical trace specialization, not a new quantum knot algorithm. |
| 8. Representation theory and symmetric functions | 12: rectangular supercharacter; 14: finite dual-Cauchy partition sum | The short Jacobi–Trudi determinant needs precisely the long modular remainder; explicit partition summation is expensive. |
| 9. Fermionic statistical mechanics | 13: exterior/Berezin Gaussian and source insertion | Exact determinant and marked resolvent; the Jh modes remain. Small tensor description does not imply small matrix rank. |
| 10. Graph zeta and nonbacktracking walks | 15: weighted Bass–Ihara reduction | The desired residue is a vertex trace. A rank-one tensor core is explicit, but its correction contains the original singular input and can cancel native zeros. |

Detailed finite identities and their scope are in [joint-lambert.md](joint-lambert.md), [torus-query.md](torus-query.md) and [exotic-forms.md](exotic-forms.md). Old q-series, moment, AW, trace and labelled-algebra work keeps its prior credit. The catalogue is not presented as fifteen new discoveries.

## Positive pieces folded into the hybrid

The [integration proof](hybrid-integration.md) keeps the original coupled/tagged branch and the new torus-only branch separate where their promises differ.

1. **Torus-only coverage and recovery now compose.** Use actual roots W^(ell-a-bN), clock W^H and the original weighted row window. The own witness exponent is -(R+1)(a+bS), a nonzero integer. A separate short clock screen permits removal of literal-zero rows. Every remaining local torus alias can be localized and consumed by the paid torus-annihilator decoder. No colour tag is needed in this branch.
2. **The tagged branch now needs values only.** For A_j=G_h(T_j), multiply (A_j,1,w_j) in a constant three-coordinate jet algebra. The resulting d0,d1,dw give a valid tag ratio after the essential d0=0 gate. This removes clock-derivative and q-binomial-normalization acquisition from the old Lambert completion. It does not improve the long value engine's exponent.
3. **There is a computable adaptive speedup.** Group integer exponent APs by residue, merge intervals, and optionally identify E with -E. If the resulting mass S is soft O(K²) in a correct bin, the query and recovery cost soft O(K). Acquire all bin metadata first and try qualifying bins before expensive fallback. This is a conditional algorithmic theorem; no uniform mass bound is asserted.

For the torus branch, with t=W+W^-1 and Delta=t²-4 a certified unit,

    Norm(W^E-1)=2-C_E(t)=-Delta*L_(E/2)(t)^2,
    L_(m+1)=t*L_m-L_(m-1).

All native E are even. Each row s_j(i)=L_(d_j-(H/2)i) obeys the SAME scalar order-two recurrence with coefficient Tr(W^(H/2)). This supplies a concrete acquisition problem with complete recovery, not merely a representation name.

## What was actually tried

The reports execute six candidate contractions on their actual input requirements: short Padé quadrature, joint modular remainders, scalar Lucas initialization, AP-support union, supercharacter determinant compression, and Bass graph/tensor compression. The root also proves the value-only gate and its public-label resultant. Only the support-union route gives a new adaptive time bound; none gives the required uniform soft O(K) bound.

The [structural experiment](audit-torus-query.md) implements exact integer Gauss reduction and interval union on 116 bank/bin fixtures, e=3,...,9 and K=54,...,39366. It checks the Hermite bound, coefficient bounds, phase and derivative congruences, own-colour window and nonzero witness. It acquires no group point or unknown order and does not run a factoring-success campaign. Ordinary unions retain 0.8765–1.0 of the original Jh mass. Inversion saves nothing further in the sampled correct-factor bins. The normalized sqrt(S)/K rises from roughly 3.82 to 19.72. These observations are not an asymptotic lower bound and do not establish a universal failure of more sophisticated support contractions.

The root [finite-identity checker](check_exotic_identities.py) verifies 30 exact cases modulo 1009, including repeated numeric row roots and collisions: supercharacter equality, shifted remainder band, Bass determinant identity on its unit locus, tensor determinant and characteristic-polynomial transform. All pass. A further 60 exact checks verify the normalized rank-one source identity, and seven Lucas rows verify the finite-part hit flag, with 112 regular-parameter checks of its regulated identity. In ten deliberately included collision cases, the graph determinant alone is nonzero while the native product is zero. These are algebraic diagnostics, not native semiprime counterexamples; they demonstrate why its correction cannot simply be discarded.

Reproduce the structural data with:

    python3 check_support_union.py --max-e 9 --output support-union.json

Reproduce the algebraic diagnostics with:

    python3 check_exotic_identities.py

The scripts use only the Python standard library. The table outputs are [JSON](support-union.json) and [CSV](support-union.csv); the identity results are [exotic-checks.json](exotic-checks.json).

## What remains

The strongest remaining targets are the original singleton readout without acquiring all row factorials, or a simultaneous zero-support algorithm for the acquired Lucas streams. Both have a paid downstream consumer. Their uniform acquisition still costs soft O(K^(5/4)); no complete soft O(N^(1/6)) bit-complexity proof follows from this pass. Literal overlap on the tested banks supplies only constant savings. The graph and supercharacter structures are candidates for a future contraction, not installed fast engines.

Independent reviews: [torus](audit-torus-query.md), [Lambert and value-only gate](review-joint-lambert.md), [exotic forms](review-exotic.md). The Lambert pullback correction T_j^-1 C((1+delta)/T_j) is applied. Source metadata and scope are in [sources.json](sources.json), validation status in [review.json](review.json), and immutable file pins in [manifest.json](manifest.json).

## Direct-residue follow-up

The user's subsequent six-barrier summary is treated as evidence about particular constructions, not a general impossibility result. See [the direct target](direct-residue-target.md), [selected local duality](direct-selected-residue.md), [the graph source insertion](direct-graph-residue.md), and [Lucas finite parts](direct-lucas-readout.md). The source insertion gives two fixed scalar determinant values equal to the gated readout; the Lucas identity isolates the count as a finite-part correction. Neither has yet been evaluated in soft O(K). The other report's exact scalar C has not been supplied or located, so no equality with that symbol is claimed.

Additional independent review: [selected residue](review-direct-selected-residue.md); the graph source identities were independently reviewed by the q-holonomic agent, and the Lucas identities by the root, with exact diagnostics above.
