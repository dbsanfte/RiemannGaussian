# Physical source execution and control joins

The final original-source entry point is `SourceInterpolationGeneratedBits.acquire A R a y k`, with coefficient correctness for k<R+1. It constructs the actual interpolation expression, invokes the tracked generator once, encodes its returned original literal bank, lowers its returned code, executes the existing Boolean interpreter and physically reads the acquired output descriptor. Source construction remains a native interface with its earlier original state/height bounds; it is not charged as Boolean execution by this packet.

## Address translation and original-source safety

`SourceArrayProgramLowering.address initial next id` is `next-initial+id` for an initial register and `next-1-id` for a generated register. Initialized IDs have addresses below next. Prepending shifts every old address by one and places the fresh ID at zero. `Represents` relates the concrete list to the stable-register proof environment, and `lower_evaluate` preserves that relation over every emitted instruction. The functional environment is used only by proofs.

Lowering emits the existing fixed-width division/remainder digit loop, retaining exactly `T*(8B+17)+1` scalar/digit construction stages for T instructions. Every operand has literal width B. Choosing B=initial+T+1 suffices. These scalar stages include native bounded address arithmetic; they are explicitly distinguished from the physical interpreter clock.

`SourceArrayCompilerSafe.source_safe` derives every individual multiplication output and every convolution accumulator's Fits at `stateBits A Q R+1`. It uses original leaf representations, subtree bounds and single-term/prefix convolution slices. The final bank includes literal zero/one plus original syntax leaves; its bounds are derived too. There is no requested-output Fits premise at the final original-source entry point.

`SourceArrayProgramAcquisition.acquireBank` encodes each actual literal once and pays its canonical digit/cell report. `readout` generates the actual output address and uses the paid Boolean-address memory scan. The encoder's numerator/denominator extraction and digit division are native scalar operations at this stage, not an already-complete primitive-bit acquisition theorem.

## Generator and physical execution are joined

`SourceArrayGeneratedBits.coefficient` consumes the actual `Generation.generate` result once. It uses the returned bank, code, cached code size and `Shape.read k`. The code is not recomputed through the specification compiler for output acquisition. The generator/encoder/lowerer/readout metadata report remains distinct from Boolean execution.

`coefficient_word` and `coefficient_bitWork` identify the generated path with the reference backend because the literal emitted program and physical operations are identical. This equality does not identify scalar generation costs: `coefficient_acquisitionWork` and `coefficient_totalWork` explicitly add the actual generator, bank traversal and output-ID read. It also does not relate the new whole-program runtime to the earlier public caller.

`SourceInterpolationGeneratedBudget.acquire_work` substitutes actual original syntax size, coefficient width and bit-height bounds. Its `work_monomial` proves input-independent C,k for the joined retained report. The important substitutions are bank length<=nodes+2, instruction count<=nodes*(J*(J+1)+J), nodes<=6Q²+8Q+3, J=R+1 and stateBits<=the original polynomial in A,Q,R. Exponential scalar magnitudes are not renamed as polynomial resources. The generic scalar metadata ledger can mention arbitrary k, but actual coefficient correctness requires k<R+1; a primitive-bit metadata refinement must retain that index bound.

## Physical comparison and dynamic source control

`SourceComparisonBits.compare` computes numerator/denominator cross-products and uses the existing signed Boolean comparator. Positive encoded denominators suffice for exact rational order. It handles signed zero and equality without canonical reduction, GCD, output fitting or rational-value decoding. Product words have width<=3W and reported comparison work<=200(W+1)².

`SourceChoiceBits.choose` follows the original tail-first recursion. Both score producers execute at each comparison; their clocks, direct comparison and selected-ID copy are all retained. Every returned ID is in the original candidate list. The original left-on-equality choice is preserved.

`assign` consumes a physical unary-token list, selects one ID, copies the complete updated prefix and proceeds along that branch. It does not expand a tree of all possible assignments. `run` first acquires the tokens, paying 2n+1 constructor/control stages. Exact choice/assignment refinements and label-decoder composition are proved. Polynomial control bounds require the score producer's value/validity/width/work contract; acquiring that producer from the actual original objective remains open. The decoder in the composition theorem is specification-only, not a runtime access oracle.

These modules lower useful actual source blocks and control. They do not claim that all source arithmetic, native metadata, auxiliary machine states or the original N-only public caller have been joined.
