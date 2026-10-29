# Numeric backend resource substitution

The new `SemiprimeSourceArrayBackendBudget` imports only SourceProgramStorage. Its `envelope M T V b` is exactly the sum of the two right-hand sides of SourceArrayProgramBits.coefficient_work, with literal-bank length M, instruction length T, frontier V and scalar width b. `envelope_mono` proves simultaneous componentwise monotonicity in a semantic-free natural-number context. `diagonal_monomial` proves fixed monomial growth with constants chosen before all inputs.

The original SourceInterpolationProgramBudget statement is preserved. Its source_resources theorem still derives actual bank/code/frontier/width bounds from original A,Q,R. acquire_backend_work now combines the actual coefficient work theorem and applies envelope_mono directly, avoiding expensive source-expression unification inside gcongr. backend_monomial remains the original fixed-resource polynomial theorem.

These bounds cover the displayed acquisition and physical backend ledgers. They do not silently add AST generation, source scalar production, or a whole machine bit-clock theorem. The generated-program and original-source joins are separate modules owned by root.

Both canonical strict builds and ordinary-root namespace lint/all-generated transitive axiom checks passed: 20 declarations, 14 theorem constants across these two modules; only propext, Classical.choice and Quot.sound. Isolated recompilation and final source/object hashes are recorded separately.
