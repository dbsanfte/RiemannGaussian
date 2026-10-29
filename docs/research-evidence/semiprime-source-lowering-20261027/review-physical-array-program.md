# Independent review: lowered original source interpolation

Disposition for frozen Lowering/Acquisition/ArrayProgramBits/InterpolationProgramBits: PASS. These four reference-backend sources are now pinned. The NEW separate GeneratedBits/original-source generated endpoint and budget are reviewed in the FINAL addendum below. This review does not assert a public-controller path replacement or complete primitive clock.

## Stable register lowering

`address initial next id` correctly separates the two layouts: initial bank IDs map to `next-initial+id`, while newly allocated IDs map to `next-1-id`. Thus initial order is preserved below the reverse-ordered fresh prefix. At the initial frontier the map is identity; each prepend shifts every old initialized address by one, and the fresh ID maps to zero. The finite `Represents` relation includes actual memory length and every initialized stable register. `represents_step` handles fresh and old IDs separately, with no desired environment correspondence premise.

The emitted operand words are actual `digits B` outputs. `address_lt` plus the total-frontier bound ensures exact digit encoding, not reduction/truncation of an oversized ID. `lower` visits each instruction once at its actual frontier, preserving opcode and both operands, and its precise generation ledger includes both digit loops. `lower_evaluate` and `lower_safe` maintain the relation at every actual stable-register update and physical prepend. Generic Safe is an explicit interface here; the actual source instance below discharges it, so it is not hidden advice.

## Actual literal acquisition and readout

`acquireBank` encodes the actual original rational literals once per list cell and retains their scalar/digit reports. Original numerator/denominator ≤2^bits guarantees exact value at physical width bits+1, including endpoint equality. No pre-encoded bank is supplied. Its value/validity/shape/width bounds are linked to actual recursion. Canonical extraction and digit generation remain explicitly scalar stages, rather than being mislabeled as Boolean primitive steps.

Readout generates the stable output address and uses the actual Boolean-address scan/copy primitive. Correctness needs initialized ID<frontier; this is supplied by program_spec for k<J. Width/validity also cover the literal default generically. The chosen B=frontier+1 is deliberately conservative but finite and polynomial in actual code/bank size. The acquisition and scan ledgers stay distinct.

## Current complete physical coefficient call path

The actual expression is supplied, not a compiled coefficient answer. Runtime acquires bank, constructs source code, lowers addresses, executes the physical VM and physically reads the selected output. Generic coefficient_correct assumes only the explicit original bank bounds and Safe interface. The original interpolation wrapper supplies both unconditionally: constants come from actual executed parity/prescriptions, source_literal_bounds bounds each leaf; source_safe proves every individual product and partial accumulator at stateBits+1 from original full-tree caps. No intermediate Fits, encoded word bank or precomputed coefficient oracle remains in the ORIGINAL wrapper's correctness theorem.

`acquire_correct` matches the exact original row coefficient at k<R+1 and returns validity+physical width. Degenerate original dimensions are covered by the unconditional leaf/node theorems; no extra probabilistic/genericity gate is imported. Source_dimensions bounds actual bank/code sizes from original syntax nodes.

## Cost and integration boundary

The first runtime version's acquisitionWork counts literal encoding, address generation, templates and readout, but not all AST program construction, literal-ID lookup or output closure access/recomputation. The NEW separate generated-runtime endpoints use the acquired tracked generator and paid Shape.read; their FINAL addendum below credits that actual acquisition. The four earlier files remain a reference backend. Repeated source/frontier/output calculations cannot silently be treated as cached free functions. The raw scalar source expression/parity/prescription construction is also a separate interface even after code generation is paid. In particular, a tracked literal-position scan using DecidableEq ℚ has a real scalar equality stage; original leaf binary-height bounds make a bit refinement plausible but its unit scalar ledger is not already a physical Boolean equality implementation.

The physical bit ledger genuinely includes actual interpreter arithmetic/scans/persistent copies and final output scan; scalar metadata/encoding and original source-construction costs are not automatically primitive bit steps. There is no theorem here that replaces the existing N-only public counter with this compiler, nor a complete machine scratch/allocator theorem. These limits are consistent with the source docs.

## FINAL addendum: acquired generation and ORIGINAL endpoint

Final disposition: PASS. Reviewed frozen SourceArrayProgramGeneration, SourceArrayGeneratedBits, SourceInterpolationGeneratedBits, SourceArrayBackendBudget, SourceInterpolationProgramBudget and SourceInterpolationGeneratedBudget in addition to the four pinned reference modules.

The new runtime really calls `generate` ONCE. It uses the returned literal bank, cached code size and Shape output descriptor; operand instructions are lowered from that returned code. Final output ID acquisition really calls Shape.read, with its ledger included. Generation itself acquires constants by actual AST traversal/paid append, performs literal-position scans, caches both child programs and emits every add/product/accumulator instruction. `generate_block` identifies this actual data with the verified compiler; it does not supply compiled answers. `generate_work` bounds actual generation reports by generationBudget using original nodes/cache length and actual emitted-block work. The old-reference backend is kept separate.

`coefficient_word` and `coefficient_bitWork` express equality of the SAME literal physical backend calls after the proved generated bank/code/output equalities. They do not falsely equate the changed acquisition report with the old one: generation work, Shape.read, actual initial-length traversal and metadata allowances are separately retained. `coefficient_acquisitionWork`/totalWork bound precisely that changed scalar ledger. No arbitrary code-generation callback or free output function survives on this new path.

The FINAL original entry point is SourceInterpolationGeneratedBits.acquire, which explicitly calls GeneratedBits.coefficient on actual original source code. Its acquire_correct discharges bank bounds and source Safe internally and returns exact original row coefficient, validity and physical width with only original data and k<R+1. There is no encoded-bank, coefficient-value or intermediate-Fits premise. The earlier SourceInterpolationProgramBits.acquire remains a reference endpoint and is not misidentified as the tracked new path.

The generated budget closes original-resource substitution: source_resources derives actual bank/code/frontier/bits bounds from A,Q,R; the pure backend helper is monotone in those four independent natural caps. source_generation_work uses actual generator work and actual source node bound, not a code oracle. acquire_work sums actual generated work, reference backend work and the proved actual bank overhead. work_monomial produces fixed witnesses after unfolding the full generation/backend dimensions. Thus the coarse displayed report is genuinely polynomial in original A,Q,R resources; no exponential magnitude is quietly substituted for its bit exponent.

The resource theorem remains about the sum of explicit native scalar acquisition/generation and Boolean backend ledgers. Literal rational equality scans, original parity/prescription/source-AST construction, general native metadata-to-machine refinement and full auxiliary allocation still have their stated boundaries. Generic metadata formulas permit arbitrary k; a future primitive-bit refinement uses the already-required k<R+1 to bound that input. No N-only public factorizer path switch or complete primitive clock follows merely from this isolated original-row endpoint.

Final reviewed sources are pinned in review-physical-array-program-sources.json. No substantive correction requested. No source edits performed by reviewer.
