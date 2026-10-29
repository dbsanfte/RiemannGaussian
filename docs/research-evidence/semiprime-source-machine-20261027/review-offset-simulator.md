# Independent review: addressed offset, storage and packing

Disposition: PASS for the stated semantic, report-clock and finite-payload scope. This does not switch the existing N-only controller to this interpreter and does not close its whole primitive clock.

## Literal offset execution

Reviewed `SemiprimeSourceOffsetProgramBits`, `SemiprimeSourceProgramBits` and `SemiprimeSourceMemoryBits` against the definitions. Newest-first addresses are consistent across all twelve operations: y², y²M, y²M², U inverse, first quotient, x², x²Q, x²Qn, x²Qn², r inverse, second quotient, sum. Every operand address is the actual four-bit little-endian descriptor used by the interpreter. Both operands are scanned even for inversion. Each step physically executes the existing word circuit and copies the old store. The supplied `Safe` predicate in the generic interpreter is discharged at this concrete source instance from ORIGINAL representations and offset scratch bounds, with reciprocal U and r handled explicitly, U>0 following r>0.

`run_offset` assumes only legitimate original acquired word values/validity/width, not computed intermediate Fits or an answer. Its 7→19 register count and twelve-step bound follow the same literal program. `caller_safe` uses the actual scheduled source scales, including universal alphabet U=r^(2Q); it does not substitute the candidate-word alphabet r^Q. Initial acquisition/encoding is correctly separate. There is no original-controller call-path replacement theorem in this module.

Important width qualification: this implementation currently chooses W=height+1 from a *magnitude* cap. It proves a finite valid execution and a clock polynomial in W. It does not prove W polynomial in original binary input lengths. For the sixth-rate goal, a logarithmic-width sharpening is NOT necessary: actual scheduled d,B,U are polynomial in the existing public resource sum, which already includes U. An explicit substitution of those original scheduled resource bounds into height suffices; it is now closed by the separately reviewed SourceOffsetProgramBudget below. Original word acquisition remains separate.

## Persistent storage

`SourceProgramStorage.stores` follows actual `step` on each recursive edge, including the initial and final memory. `stores_bound`, `run_mem_stores` and `all_store_cells` therefore concern actual execution states, not states selected by a desired height premise. The length cap is original memory length plus instruction count; width inheritance is physical output truncation plus copied original widths. Correctness of numerical values remains the separate Safe-based theorem. The sum counts all persistent memory payload versions conservatively and does not assume destructive mutation or GC. Code payload counts the two actual address lists and a fixed opcode allowance.

`resource_polynomial` is a genuine fixed polynomial in its memory/code/width/address caps. It omits arithmetic-circuit scratch from the persistent-store sum (circuit clock already charged) and does not purport to count a complete tape/reference/header implementation. No stronger total-storage conclusion is being smuggled into that theorem.

## Actual packing state

Reviewed `SourcePackingState` against executed `labels`, `bucket`, `minimum`, `position`, `place`, snapshot and name constructors. No correct-packing or successful-lookup assumption is needed. Bucket members come from the cached original incidence list; missing lookup defaults are bounded as well. Every emitted block ID is below the actual minimum, itself at most incidence count; complete-block names retain an actual universal key, and leftover names retain an original incidence. Snapshot addresses are definitionally the original materialized scans. Actual labels, addresses and names have the stated M, M, and ≤MD+M row counts.

Allocation counters follow the same conditional cons/append recursions: bucket cons, bank cons, block-name copies, leftover collects and names append are bounded by the corresponding ACTUAL reports. These are specific cells/records, not a claim that their sum is all allocator traffic. Expanded `retainedCells` deliberately counts universal coordinates repeatedly across shared references; its polynomial bound is a conservative field view, not peak machine heap. The original-caller theorem substitutes the actual searched-label producer, but is a state bound only: use of producer.value there does not pay source producer execution anew or provide a clock theorem.

No semantic correction requested. Remaining obligations are original acquisition, full reference/address/tape treatment and actual controller integration; they are not assumptions hidden in the reviewed statements.

## Final addendum: original-resource offset budget

Reviewed FINAL `SemiprimeSourceOffsetProgramBudget`: PASS. `scheduled_width_le` bounds actual scheduled d=r*lam*U*2r by 2S^4 and B=2Mr+n*r*lam*U by 2S²+S^4, with all original dimensions and U separately ≤S. The original `height` is a polynomial with fixed nonnegative natural coefficients/powers; substituting those majorants and the original dimension caps therefore bounds the ACTUAL chosen width, without replacing a magnitude by its bit length. `caller_width_le` obtains U=r^(2Q) from the exact actual enumeration cardinality, not an invented small universal bank.

`caller_run_clock` applies the actual interpreter `run_clock` to seven acquired physical registers, twelve literal instructions and four-bit addresses; monotonicity transfers the resulting clock to `clockEnvelope S`. Its legitimate premises are only original memory length and width plus original resource caps. Value correctness still comes from `run_offset`/`caller_safe` with original representations/validity; the budget alone does not assert arbitrary memory computes the source value. `clockEnvelope_monomial` proves existence of fixed C,k after unfolding the entire selected width and primitive budget, so this is an actual original-resource substitution rather than an assumed runtime. No hidden dependence on 2^S appears.

This resolves the earlier coarse-width qualification for scheduled resource-time purposes. It does not acquire the seven initial words, instantiate a whole-source instruction compiler, or change the public controller path. Final independent disposition: PASS for all reviewed modules at their stated scope.
