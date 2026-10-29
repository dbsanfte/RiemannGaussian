# Independent source-compiler review

**PASS within the stated staged scope.** Read-only review of the eight final frozen sources listed in `review-source-compiler-pins.json`; no source or object builds/edits were performed for this review. The parent confirmed terminal canonical strict success for all eight. Central combined validation is recorded separately by the parent.

## Actual caching and initialized register semantics

`SourceArrayProgramIR.evaluate` allocates successively fresh stable IDs. `evaluate_old` preserves older registers, and `WellFormed` requires both operands to be initialized. Mathematical environments are specifications, not runtime operand suppliers. `dotCode` emits a real multiplication and then an accumulator addition for every term; zero-length dots use the original zero register. The final accumulator ID is distinct from the fresh product ID.

`SourceArrayProgramBlocks.mulCode` computes coefficients in increasing order, caching every product and sum. The count J(J+1) and output ID `start+(k+1)*(k+2)-1` agree with the exact accumulated block lengths. `mulCode_correct` proves the original finite convolution, not a supplied resulting coefficient. Addition uses only the two pre-block arrays. Operand bounds cover every k-i index in the original truncated range, including k=0.

`SourceArrayProgramCompiler.compile_spec` composes the actual left and right child blocks, preserves the left array while compiling the right, and retains the actual zero/one/literal registers. Its final `program` obtains its bank as `0::1::constants p`. Literal IDs come from first-position scans of this original traversal list; duplicate constants are allowed. `program_original_coefficient` identifies the result with the actual frozen cached `SourceCodeArrays.compile`, not merely a formally similar polynomial.

## Generator and report fidelity

The runtime is `SourceArrayProgramGeneration.generate`, rather than the semantic compiler with a separate cost tally. It acquires the constant list once, caches both recursive child results, caches code lengths with a proof that they equal the actual list lengths, and performs actual append/copy generation. Runtime output IDs use the four-case finite `Shape` descriptor and paid `Shape.read`; the semantic `Block.output : Nat→Nat` is not an arbitrary runtime callback. All bank lookups are actual finite `position` scans. `generate_bank` and `generate_block` identify the returned bank/code/descriptor with the initialized compiler.

The reported generation bounds retain both child reports and both code-copy stages. In particular, `join_code_size_work` and `assembleAdd_work`/`assembleMul_work` account for copying the left child into the combined children and copying that combined code into the final block. The closed generator budget is fixed polynomial in syntax nodes and J; it is not a per-coefficient recursive expansion of the source AST.

## Original-derived safety

`SourceArrayProgramSafe.dotCode_safe` checks BOTH the stored multiplication result and every chronological addition prefix. `mulCode_safe` covers every emitted coefficient. The internal exact-expression `*_safe_known` lemmas are compositional tools, not final advised-Fits hypotheses.

`SourceArrayCompilerSafe` discharges those internal conditions: a multiplication term is a length-one original convolution slice; each accumulator is its actual finite prefix. Thus cancellation in the final coefficient is never used to license unsafe intermediate arithmetic. Addition results are actual parent coefficients. The same original full-tree denominator/numerator cap covers all children and all stored intermediates.

`source_safe` derives strict Fits at `stateBits A Q R+1` from the original executed parity source, original leaves and node cap. The extra bit converts non-strict dyadic caps into strict Fits. `source_literal_bounds` also derives every original literal's reduced numerator/denominator cap. No source coefficient, encoded-bank, or intermediate-state answer is supplied to the final source specialization.

## Generated physical entry point

`SourceArrayGeneratedBits.coefficient` caches `generate` once, encodes that returned bank, lowers its actual returned instructions, executes the physical interpreter and obtains the final ID through `Shape.read` followed by the paid physical memory scan. Its `coefficient_word` and `coefficient_bitWork` equalities are legitimate: the two compared executions have exactly the same bank/code/readout operands, not merely the same mathematical output value. The new generator and ID-read work remain in `acquisitionWork`; `coefficient_totalWork` adds that work instead of transferring an old whole-clock theorem by value equality.

`SourceInterpolationGeneratedBits.acquire` calls this generated physical path directly on the actual original source expression. `acquire_correct` has only original dimensions/types, the requested in-range coefficient, and no residual bank/Fits/value premise. `acquire_work_components` retains generator work together with both backend ledgers.

## Exact remaining boundary

Generation, rational equality in literal scans, Nat metadata/ID arithmetic, original parity/prescription/AST construction, and canonical rational digit extraction are explicitly native scalar interfaces. The reviewed work statements do not turn these into primitive-bit operations at unit cost. The original source constructor's own report is not silently present in `acquire_work_components`: it must be joined separately. Original source types/input encoding, the actual score-producer/caller composition and a whole public primitive-machine clock remain separate. Physical comparison/choose control exists in other new modules under its score-producer interface.

This distinction is consistent with the source headers and author notes. No theorem or runtime call in these eight sources assumes a source cost oracle, supplies an intermediate Fits answer, queries a mathematical coefficient oracle, or asserts that the old public factorizer has already switched to this path. No correction is required.
