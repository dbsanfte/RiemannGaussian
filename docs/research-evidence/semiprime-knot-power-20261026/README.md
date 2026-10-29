# Independent knot weights and power-level acquisition trials

26 October 2026. **No improved guaranteed acquisition exponent.** The current native query remains softly O(k^(5/4)), with the previously paid wheel saving. The desired softly O(k) bound, and the all-semiprime sixth-exponent theorem, remain open.

This pass identifies a concrete surviving knot candidate: reciprocity places every adjacent pair of desired weights on the same rank-four resonance of a diagonal Nichols model. We verify its finite invariant vector, action and coaction. Its normalized knot amplitude has not been shown to preserve the collision predicate, and no composition law contracts all pairs cheaply. A tempting different deformation fails an explicit Yang–Baxter coefficient; that mistake was found and corrected during independent review.

## Contract and useful distinction

The acquired ordinary Alexander polynomial K has Laurent support [-L,L], with L=soft(k), and the query is

    P_m = product_(i=1)^m K(eta^(2i+1)),
    q=eta^2, m=Theta(k^(3/2)), k=Theta(N^(1/6)).

The initialized geometric-product cost is soft(L+sqrt(Lm)). A sufficient target is soft(L+sqrt(m)), with all construction, finite boundaries, zero-divisor handling and original-leaf recovery included. Having a short representation of P_m is not yet an algorithm with this cost.

## Results and reviews

| Investigation | What is established | What remains |
| --- | --- | --- |
| [Supergroup specializations](supergroup-product.md) ([review](supergroup-review.md)) | Proved Links–Gould specializations give a single Alexander value or repeated equal arguments. Latest colored-LG v3 checked. | They do not aggregate the distinct native arguments. |
| [Independent weights](independent-weights.md) ([review](independent-weights-review.md)) | The ordinary exterior tensor model gives the exact independent-argument product; the Seifert Kronecker determinant preserves collisions. | Expanded ranks are 2^m or 2Lm; fast scalar contraction is unpaid. |
| [Reciprocal adjacent-pair resonance](coupled-parameters.md) ([review](coupled-review.md)) | t1=eta^(2i+1), t2=eta^(-2i-3) satisfy t1*t2*q=1; explicit rank-four diagonal Nichols span/action/coaction are legal. | Specialized braiding/normalization, the collision-preserving scalar identity and a composable algorithm. |
| [Executed two-mode deformation](two-mode-deformation.md) | Exact defect p*b^2*(p-1)*(a-b) disproves the proposed independent-weight KM-Hecke extension at native geometric weights. The p=1 tensor case survives. | A different lawful coupled construction is required; this is not a general no-go for knots or factoring. |
| [Cyclic dilogarithm and axis factorial](axis-shortfactorial.md) ([review](axis-review.md)) | Exact off-root boundary identity; a known soft-k smooth-order branch is safe under the pinned coprime-order controller. | Singular interior quotient and all remaining prime/two-large-prime order cases. |
| [Character/CRT compression](character-compression.md) ([review](character-review.md)) | One-prime Fourier formula and exact carry accounting. | At power-level sieve strength the modulus exceeds the entire clock, leaving an unacquired carry/cutoff contraction. |

## Literature priority

The most specific follow-through is [Garoufalidis–Kashaev, multivariable knot polynomials](https://doi.org/10.4171/PRIMS/62-1-3), Section 7.3: derive the complete specialized four-state map for the reciprocal pair and calculate its normalized scalar before attempting repeated fusion. Its equation (101) states a two-Alexander product, while the published summary table marks the same identity with a question mark; this packet records that discrepancy rather than relying on it. The independent tensor proof is separate.

[Kashaev–Mangazeev's exterior-algebra formulas](https://arxiv.org/html/2505.15569v1) supplied the explicit local calculation that exposed the failed deformation. Independent diagonal scaling commutes with the braiding simultaneously, but the categorical construction also needs separate naturality. These conditions differ in the presence of an exchange term. The source's scalar-weight construction is not being challenged.

[Kohli–Patureau-Mirand](https://arxiv.org/abs/1606.02538), [De Wit–Ishii–Links](https://msp.org/agt/2005/5-1/agt-v5-n1-p18-p.pdf), and [colored Links–Gould v3](https://arxiv.org/html/2509.10911v3) give precise specialization boundaries. [Garoufalidis–Kashaev's cyclic dilogarithms](https://arxiv.org/abs/1411.6062) supply exact finite identities but no initialized sub-square-root axis product. Full source metadata and available scratch fingerprints are in [sources.json](sources.json).

## Interpretation and integrity

This is a representation refinement and a set of executed candidate checks, not substantive progress on the required whole-family complexity bound. No finite example campaign, Lean/backend expansion, public asset build, commit or push was used. The familiar smooth-order and wheel branches receive prior-method credit. The dependency-free [symbolic checker](verify_symbolic.py) verifies the displayed determinant, the exact defect coefficient, and both lawful specializations on every basis word, as polynomial identities rather than numerical samples. Frozen evidence and the existing journal/guide prefixes are preserved; [review.json](review.json) records the validation scope and [manifest.json](manifest.json) fingerprints this packet.
