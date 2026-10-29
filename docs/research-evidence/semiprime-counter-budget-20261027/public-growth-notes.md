# Public controller/scalar monomial growth — completed

NEW `SemiprimePublicReportGrowth` imports the frozen concrete public controller/scalar envelope definitions and the proved fixed-arithmetic closure.

`controller_monomial` proves `∃ C k : Nat, ∀ S, controllerEnvelope S ≤ C*(S+1)^k`. It reuses the actual setup+native sum bound as `Bound countEnvelope` and explicitly applies sum/product/fixed-square closure to the literal controller expression.

`scalar_monomial` proves the identical form for `ScheduledScalarBudget.scalarEnvelope n`, fully unfolding its concrete entry/scope/decoder expressions before the proof-producing syntax-directed closure. Neither theorem assumes a cost oracle, polynomiality hypothesis, fast guard or desired output. Their constants/exponents are fixed independent of the input.

These are numeric uniform growth results. Connecting them to actual eventual resource bounds/rate and interpreting the complete primitive address/bit model are separate composition obligations; no such machine claim is made by these two lemmas.

Strict PASS; ordinary-root fifteen linters and all-generated standard-three-axiom audit PASS: two declarations/two theorem constants. Isolated .olean byte-identical canonical. Pins: public-growth-verification.json. No old sources or sealed packets modified.
