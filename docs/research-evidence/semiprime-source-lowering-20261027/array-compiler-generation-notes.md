# Actual cached source-array program compiler and generation

Four NEW modules implement and prove the actual compiler from the original finite `PolynomialCode ℚ` expression. Frozen source and prior packets are unchanged. There is no compiled-code, coefficient-answer or arbitrary constant-bank runtime argument to the final `program` / `generate` entry points.

## Cached coefficient semantics

`SourceArrayProgramIR` uses stable natural register IDs. Its proof semantics assigns each instruction a fresh ID and never overwrites an older register. `evaluate_append` tracks the exact frontier; `WellFormed` requires both operands to predate each instruction. These mathematical environments are proof specifications, not runtime operand suppliers. Actual physical newest-first addresses are handled by the separate lowering module.

`SourceArrayProgramBlocks.addCode` emits exactly J scalar additions. `dotCode` emits a product and accumulator addition for every actual convolution term; both temporary values remain allocated. `mulCode` emits exactly J(J+1) instructions for the whole coefficient vector, with result ID `start+(k+1)(k+2)-1`. Every output coefficient is the exact finite convolution sum. The zero-length cases and old-register preservation are proved explicitly.

`SourceArrayProgramCompiler.compile` recursively compiles each child ONCE and retains both cached output vectors. Add/mul then use the corresponding array block. There is no recursive per-coefficient expansion of the source AST. `compile_spec` proves initialized operands, output-ID bounds and all coefficient values. `program_original_coefficient` identifies the generated result with the ACTUAL frozen `SourceCodeArrays.compile J p`, not merely an unrelated polynomial expression.

The initial bank is literally `0::1::constants p`, where constants are extracted from the original expression in traversal order. Duplicates are allowed. Each constant ID is computed by finite first-position lookup in that original bank. `bank_literals` and `program_spec` discharge the initialization conditions; no bank lookup answer is assumed. `bank_representation` derives all bank representations from original source leaf bounds, including the literal zero/one registers. The generated code length is at most `nodes p*(J*(J+1)+J)` and bank length at most `nodes p+2`.

## Actual generator, not an independent tally

`SourceArrayProgramGeneration.generate J p` executes a paid original-leaf traversal once, caches its list, performs the actual rational first-position scan for each constant leaf, and builds all scalar instruction lists through recursive append/copy operations. Output IDs are represented by one of four concrete `Shape` formulas; instruction generation calls `Shape.read`, computing the IDs and retaining its fixed scalar arithmetic/branch work. Cached code-length metadata is proved equal to actual list length.

Every child acquisition, literal scan, ID read, convolution/add block construction, append copy and final bank-length scan is retained. `generate_bank` and `generate_block` prove that the returned actual bank and block equal the initialized original compiler. The runtime does not call the semantic compiler for its requested result and attach a separate cost.

With N=`nodes p`, the closed bound is

```
unitWork(J,L,N)=3L+6+6N*(J*(J+1)+J)+300*(J+1)^3+50
generationBudget(J,N)=5N^2+N*unitWork(J,N,N)+N+7.
```

`generate_work` proves this for the ACTUAL generator with no callback-cost premise at its final entry point. Add generation is bounded by `60*(J+1)^2`, dot generation by `80*(len+1)^2`, and full convolution generation by `200*(J+1)^3`. These are scalar/list/metadata stage counts. Rational equality during literal scans, Nat arithmetic and counter bookkeeping are not silently claimed to be primitive-bit operations. Their values/bit heights and a complete implementation simulation remain separate. The cached source syntax/leaf construction itself must also be acquired by the original-source caller rather than assumed free.

## Original-source and physical joins

The separate `SourceArrayCompilerSafe` module derives all intermediate fits from original source leaf/subtree/convolution bounds. The separate physical lowering converts stable IDs to actual prepend-relative Boolean addresses, preserving semantics. The actual SourceInterpolationGeneratedBits wrapper now composes these at the original source interpolation expression, and SourceInterpolationGeneratedBudget derives its resource-only work envelope while retaining this generator's work. The original node cap, leaf bounds and all intermediate Safe conditions are discharged in that composition.

Original offset scales and their initial words are now acquired by OffsetInputs from original natural dimensions, including an actually materialized universal-bank cardinality. Physical comparison and dynamic choose/control execution are also proved in the separate source-control modules. These achievements do not silently replace the original full source caller: the paid score producer remains an explicit integration interface. Physical parity/prescription and native source-AST/constant acquisition, native compiler metadata/address construction, the remaining caller/score-producer composition, and a complete whole-machine simulation are still open joins. This is a constructive compiler/refinement, not a query exponent improvement or a complete switch of the old public source caller. No new factoring examples or numerical scaling campaign was run.

## Validation

All four sources are FINAL FROZEN. Strict canonical builds, ordinary-root 15 linters, every-generated-declaration transitive standard-axiom checks and byte-identical independent isolated objects PASS: 440 declarations, 255 theorem constants. Exact source/object/isolated pins are recorded in `array-compiler-generation-verification.json`. No custom axiom, sorry or native_decide is used.
