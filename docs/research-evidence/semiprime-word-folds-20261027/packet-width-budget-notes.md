# Fixed-polynomial packet widths — completed

NEW `SemiprimeWordPacketWidthBudget` imports only frozen Width/NativeInputBits/ReportPolynomialGrowth modules. No physical caller or current word-packet counter is imported, so the helper introduces no execution dependency cycle.

`factorExponent_mono`, `exponent_mono`, `groupWidth_mono` and `packetWidth_mono` prove explicit componentwise monotonicity from the actual fixed arithmetic formulas. `envelope S=packetWidth S ... S`, `packetWidth_le_envelope`, and `envelope_monomial` yield fixed natural witnesses C,k with `∀S,envelope S≤C*(S+1)^k`. This is a proved numeric property of the concrete runtime-width function, not a supplied polynomiality/cost hypothesis.

For original source dimensions, b is only polynomially bounded by S; assuming b≤S would be wrong. `sourceEnvelope S` therefore substitutes `NativeInputBits.polynomial S S S S S` for b and S for the remaining packet resources. `source_width_le_envelope` derives this bound for the ACTUAL `inputBits n B Q R J` under original dimensions/cardinality bounds. `source_envelope_monomial` again constructs fixed C,k. Both monomial proofs explicitly unfold the finite formulas and use the frozen kernel-checked arithmetic closure, including all group/factor/source-width terms.

HeadCap, actual summaryCount Y and weighted support count Cq occur only polynomially. There is no `2^Y`, `2^Cq`, full `2^n` width, intermediate fit premise or arbitrary callback-clock assumption. This numeric result does not itself acquire those counts, execute a physical caller, compose the actual new report rate or prove a full primitive-bit/address theorem.

Final strict / ordinary-root15 / all-generated transitive standard-three-axiom audit PASS: 10 declarations, 8 theorem constants. Isolated object byte-identical to canonical. Pins: packet-width-budget-verification.json. Old sources/packets unchanged.
