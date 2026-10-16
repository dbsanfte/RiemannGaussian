# Independent exact-file coprime-refinement review

Verdict: PASS, no correction requested. All six exact prerequisite pins match their stated files. No build or new Lean certification is claimed.

Reviewed final targets:
- `coprime-refinement.md`: 9447 bytes; SHA256 `d4477d8a27050922f50354ca89f075b9d246adfc608eb9b486f01be4b4a74c76`.
- `coprime-source-pins.json`: 1262 bytes; SHA256 `e85889558e05cb38b60ddd2d663fddb2f9dcabc81ce454f332bb35415b3174fa`.

The theorem preserves the explicit balance and sixth-root scale assumptions needed by the extractor, and the numerical assumptions needed by uniform preprocessing. Its fixed sequence of soft-O(m) subroutines is fully supplied with inputs. No strong-order or annihilator oracle is silently assumed.

The N-1 projection proof is correct for arbitrary local orders dividing P-1 and Q-1. With g=gcd(P-1,Q-1), raising any corresponding local units to N-1 gives orders dividing (P-1)/g and (Q-1)/g. These quotients are coprime; no local primitive-root or prime-order hypothesis is needed. Oddness is preserved. This is already compiled algebra in SemiprimeOrderSeparation, correctly credited.

On an exact common-order detector output, coprimality forces c=1, so the computed beta=gamma^(N-1) is globally one. K=N-1 is then an ACQUIRED nonzero short global annihilator of the ORIGINAL gamma, whose odd-order/small-index promises remain available. Calling the standalone extractor here is sound and not circular. The NoHit branch gives BOTH beta orders>B; their small indices follow anew from the factor-size bound, and coprimality makes the global order their product>B². Composite odd orders and shared factors with indices cause no gap.

For q=beta^(m²), local orders divide the respective beta orders and remain coprime. A common exact detector output would have to be one, forcing both beta orders to divide m², contrary to their lower bounds. Thus this call either factors or proves BOTH q-orders>B. This simultaneously establishes every stated 1-q^k scalar as a unit; it does not invert arbitrary algebra elements. No gcd(m,beta-order) premise is required.

Uniform preprocessing, two detector calls, public powers and the at-most-one extractor call give the displayed soft-O(m) bit bound. The exponent31/192 is strictly below1/6 at the stated m scale, and the extractor's finite fallback is retained. The returned beta is unchanged by its q-step certification.

Historical scope is accurate: the N-1 identity and algebraic factor-or-long routing are old. I independently inspected the native order-separation module and journal passages covering the October2 stage, later local-order routing and COMPLETE October3 recursive kernel descent. The old bounded32-base unresolved status is not treated as current. The new composition is direct SAME-input paid closure using the new supplied-annihilator extractor, plus direct q-unit certification; it is not first algebraic kernel resolution.

The final limits are essential and correctly stated. This new base is not identified with literal old projected base2. No original collision/source-family coverage is transported merely from its order properties, and no long-query acquisition, full sixth-rate factorizer, new Lean declaration or native edit follows.
