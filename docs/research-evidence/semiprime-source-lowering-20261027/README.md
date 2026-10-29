# Original source compilation, offset acquisition and dynamic control, 2026-10-27

Status: **verified constructive progress; guaranteed full original-input primitive-bit scaling remains open**.

The source interpolation coefficient now has an executable path from its original dimensions and row data through acquired code generation, literal-word acquisition, Boolean-address instruction execution and a physical output scan. The final entry point is `SemiprimeSourceInterpolationGeneratedBits.acquire`. Its correctness theorem needs no supplied instruction list, encoded literal bank, coefficient answer or intermediate-fit assumption. The original constructor bounds discharge those conditions. The acquired generator, address/literal acquisition and Boolean backend reports have a fixed polynomial bound in the original A,Q,R resources.

The generator compiles each AST child once. A J-coefficient addition emits J instructions; a convolution emits J(J+1), retaining both products and partial sums. Stable register IDs are translated to the actual prepend-relative Boolean addresses. The output descriptor is acquired and read explicitly. The earlier `SourceArrayProgramBits` and `SourceInterpolationProgramBits` endpoints serve as reference backends; the generated endpoint retains the extra generation work and avoids repeated untracked compiler/output-function calls.

The offset block also closes its initial-input interface. `SourceOffsetInputs.runOffset` constructs the universal bank size by actual replication, encodes the original natural dimensions, executes eight scale operations, acquires seven normalized input registers and executes the existing twelve offset instructions. Correctness and fixed-polynomial resource bounds now cover that entire path from the original natural dimensions.

Physical candidate selection compares signed cross-products directly, including both encodings of zero and the original left-on-tie rule. Its dynamic assignment loop consumes acquired unary tokens and copies selected IDs/prefixes. It follows only the selected branch and has a polynomial control bound. The actual original score producer is still a compiler interface.

The auxiliary-state work records actual visited memory-scan frames and copied-memory return frames, including an expanded view of pending memory tails. High-level report erasure preserves the same physical output without executing outer clock aggregation. These are specified frame inventories and erasures; primitive circuit scratch, primitive-internal report bookkeeping and the complete pointer/tape representation remain separate.

**Scope of the cost result:** code generation, canonical literal extraction and some address/control metadata retain native scalar ledgers. Original parity, prescription and AST construction, original row-data encoding, the score producer, full primitive auxiliary state and the public caller still need one complete machine-level composition. The existing public factorizer is unchanged. The earlier retained-report subpower theorem remains proved; this packet does not promote it to a full bit-time theorem.

All 24 modules pass strict compilation, ordinary-root 15-linter checks and all-generated standard-axiom audits (1183 declarations, 697 theorem constants). Final independent object identities and actual compiler-import dependency pins are recorded in the [verification record](verification.json) and [manifest](manifest.json).

Read the [compiler and generator notes](array-compiler-generation-notes.md), [physical execution and control notes](physical-source-control-notes.md), [original Safe proofs](array-program-safe-notes.md), [offset input acquisition](offset-inputs-notes.md), [auxiliary frames and erasure](memory-erasure-notes.md), and [next whole-bit joins](next-whole-bit-join.md). Independent reviews cover [compiler semantics](review-source-compiler.md), [physical array execution](review-physical-array-program.md), [comparison/control](review-choice-comparison.md), and [offset acquisition](review-offset-inputs.md).

No new long-query exponent, practical speedup, commit or push is claimed.
