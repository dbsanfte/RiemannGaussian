# Actual word packets supply common Hermite input bounds

`SemiprimeWordPacketHermiteInput.packetBits b R J arity design` is the computable parameter `2*sum_a nodeWidth b R J arity (design a)+1`. It reads original dimensions and actual finite design metadata. It does not construct the common denominator.

`actual_nodes_bound` applies the already proved physical `WordPacketCounter.node_spec` at each actual `nodeWord b a`, retaining validity, exact J length and the original per-node common denominator. The original source validity/representation, dyadic source and dimension guards, positive source denominator, and Boolean entry absolute bound are the only arithmetic premises. There is no packet-output Fits or height premise.

The proof-only common denominator is the product over nodes of `DG^(design a).r`, with `DG=(den^(sum arity))^F`. Node group counts may vary. The generic `homogenize` theorem multiplies each numerator by the product of the other positive denominators. Each denominator and numerator is bounded by its actual node-width dyadic cap; therefore the product denominator is at most `2^(sum widths)` and every homogenized numerator is bounded by `2^(2*sum widths+1)`. Sums do not multiply denominators, and no cancellation is used.

The conclusion gives positivity and the dyadic bound for that common D, plus for every actual node: valid physical words, size J, and `ArrayBound (decode words) J D (2^packetBits)`. The theorem does not acquire or execute a large rational common denominator, nor claim a complete primitive bit-time bound. The runtime contribution added by this module is solely the finite-width parameter expression.

Strict compile, ordinary-root 15-linter audit and every-generated-declaration transitive standard-axiom audit pass. Isolated strict compilation is byte-identical to the canonical object; exact counts and pins are in `packet-input-verification.json`.
