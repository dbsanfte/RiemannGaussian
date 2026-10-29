# Original offset input acquisition

This stage constructs the initial seven physical rational words from the original natural dimensions `M,n,r,Q,lambda`. It does not accept rational scales, their encoded words, or an encoded universal bank. Existing frozen sources are unchanged.

## Executed path

* `SourceOffsetInputsCore.natBits` starts at the empty zero magnitude and executes one actual Boolean increment per original natural unit. `encodeNat` adds a literal sign and denominator-one word. This is deliberately magnitude-linear; its clock is at most `20*(n+1)^2+4`.
* `unaryPower r (2*Q)` starts with one cell and actually replicates each acquired block `r` times at every stage. All appends, copied cells and length scans are retained in its report. Runtime uses the acquired list length as `U`; `r^(2*Q)` occurs only in specifications/proofs.
* `SourceOffsetInputsScales.code` takes the six cached integer words `[M,n,r,Q,lambda,U]` and executes eight addressed rational operations. They compute `x=M/(r*lambda*U)` and `y=n/(2*r)` from the original dimensions. Every operation's Fits is derived from original dimensions in `code_safe`.
* `SourceOffsetInputs.acquire` scans the actual resulting memory at seven literal addresses and executes seven actual additions by zero to normalize/copy the selected values to the frozen offset template. This step is necessary: fitting canonical rational values alone would not justify directly clipping arbitrary noncanonical raw words. All seven read reports and arithmetic reports are retained.
* `runOffset` executes the existing twelve-operation offset program on this acquired memory. Its report includes the entire initializer clock and the later interpreter clock.

`acquire_spec` gives exact `[x,y,M,n,r,Q,U]` values, legal words, exact frozen physical width and seven-register length. `runOffset_correct` gives the actual original `MaterializedSourceWords.offsetRun` value, validity/width of every final register, and length19. Both require only positive `r,lambda`, with all scalar representations and intermediate Fits derived internally.

## Resource theorem

The explicit `inputBudget` includes the unary construction; six actual encoders; all eight scale instructions, scans and growing-memory copies; seven scans/normalizations; and template/allocation/control allowances. `acquire_clock` proves this budget from the actual runtime.

`runOffset_clock` bounds the complete initializer plus the twelve-operation run by `totalEnvelope S` whenever the original dimensions and actual bank `U` are at most `S`. `totalEnvelope_monomial` supplies fixed coefficient/exponent independent of the dimensions. This is polynomial in the original materialized resources, **not** a claim that an arbitrary `r^(2Q)` is polynomial in its binary description. `caller_run_clock` substitutes the exact original source enumeration cardinality `en.types.values.length=r^(2Q)`; `caller_run_offset` substitutes both actual original caller scales.

## Scope and remaining join

The Boolean arithmetic data path never decodes a rational word to execute arithmetic and never imports a scale/bank answer. The original natural dimensions are still host natural loop/control inputs. The report covers physical rational circuits, Boolean copies and finite-cell/control allowances; lowering natural parameter/control arithmetic, template-length metadata and the initial external input to a particular tape machine is not asserted here. Their fixed-polynomial original-resource budget is the relevant later simulation interface.

This new end-to-end path has not silently replaced the old public source caller. The original source compiler must explicitly call/identify this acquired path; the original score producer, caller program composition, and any whole-source/public primitive-machine theorem remain separate. Physical comparisons and dynamic choose control are now supplied by the separate proved comparison/choice modules under their score-producer interface. No whole-goal bit-time conclusion is inferred from this stage alone.

Tiny runtime controls in `OffsetInputsSmoke.lean` test encodings0/5, a genuinely replicated bank2^4=16, the seven acquired registers `[1,1/2,1,1,1,0,1]`, and final offset1/4. These are circuit controls, not factoring/coverage examples or timing evidence.

Final verification: all four canonical strict builds PASS. Ordinary-root15 plus every generated declaration audit PASS198 declarations/123 theorems, standard3-only. Final smoke output matches the five recorded controls. Exact source/object/evidence pins are in `offset-inputs-verification.json`; no further source edits planned.
