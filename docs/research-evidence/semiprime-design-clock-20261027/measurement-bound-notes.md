# Measurement height envelope — completed

`SemiprimePaidMeasurementBound.bits B Q R = B+2+2*R*(Q+3)`.
`bound_le` proves the actual `SemiprimeAcquiredSourceCounter.measurementBound B Q R = B*2*(8*Q)^(2*R)` is at most `2^bits`, uniformly including zero parameters. `integer_bound` transfers an actual integer natAbs source bound to this envelope.

The proof uses `B ≤ 2^B`, `Q ≤ 2^Q`, monotonicity of products/powers, and exponent arithmetic. It requires no entry/coefficient advice, no nonzero parameters, and no asymptotic assumption. This is an integer-capacity theorem, not an execution clock or a proof that parameters/entries have been encoded.

Strict compile PASS; ordinary-root 15 linters PASS; all four generated declarations (three theorem constants) have only standard transitive axioms. Isolated object byte-identical to canonical. Source and object pins: measurement-verification.json. Metadata ownership was handed to root before this module was implemented; this report makes no claim about its gates.
