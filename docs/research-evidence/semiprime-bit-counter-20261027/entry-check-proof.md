# Whole ordered macro entry checker

Owned NEW source `RiemannGaussian/SemiprimeMacroEntryBitCheck.lean`; the two previous entry modules and all frozen graph/semantic/counting sources are unchanged.

## Closed entry interface

`localRun` implements every literal original-graph vertex using actual Boolean-list arithmetic: source/padding/unique flags, first DFT, explicit twiddle, normalized second DFT, product, INTEGER carry with strict physical bounds, endpoint zero checks, OR and terminal true checks. `allRun` is an executed finite AND traversal. `guardRun` branches on actual canonicality gates before evaluating modular expressions. Invalid words are not supplied as promises; they fail the gate.

`localRun_correct` proves equality with the frozen `localTable` for every vertex and every local bit assignment. `entryRun_correct` transports this to the actual ordered Fin ports (`localSlotFinEquiv`). `publicBitEntry_correct` identifies the new actual bit checker with the frozen public-N tensor table. This is no longer a component-only DFT or decoder interface and supplies no desired entry-evaluator conclusion as an assumption.

The actual Fermat modulus is constructed with the existing bit routine; literal roots/inverse roots/normalizers are compiled expressions with proved canonical validity and exact macro-ring values. `Targets` contains the literal read-only public target words and their width/value invariants. `configTargets` explicitly produces them from public Config digits; for actual N they are precisely its fixed radix bit chunks. No unknown factor, hidden prime field, inverse oracle or noncomputable Boolean evaluator occurs in the checker data path.

## Closed finite backend ledger

Every comparison, modular expression interpreter, integer carry, Boolean flag and finite check-loop clock is composed. `entryRun_polynomial` bounds every assembled backend run by `2^20*(n+2)^10`; `publicBitEntry_polynomial` specializes this to `2^20*(64*bitLength N+2)^10`. The derivation uses only actual public shape/capacity theorems; it does not assume a polynomial local-entry oracle.

The source additionally proves the finite preparation facts used by the adjacent paper-level simulation: actual arity <=4(n+1)^2, gather envelope <=4(n+2)^2, expanded DFT syntax <=32(n+2)^6 over all outputs, and literal-cell allocation <=nodes*W under physical literal widths. Root/normalizer/DFT compilation preserves those widths.

`entry-preparation-cost.md` gives the explicit flat-binary implementation and constructive full polynomial bound, including descriptor generation from N, input linear lookup, syntax/literal preparation, loop/index arithmetic and pointer flattening. Its conservative bound is `2^120*(64L+2)^40` bit time and `2^40*(64L+2)^14` space. This last flat-tape simulation is a paper proof, not a formal Lean TM-compilation theorem. The formally counted Run clock intentionally remains the detailed backend clock; it is not silently relabelled as the entire native Lean evaluation time.

## Validation and files

Strict autoImplicit=false/warningAsError=true compile PASS. Root import plus all 15 scoped linters and all generated/transitive axioms PASS: 301 declarations, 231 theorems, only propext/Classical.choice/Quot.sound. Source/checker/build/audit hashes are recorded in entry-check-hashes.json.

Eight focused actual execution controls PASS in entry-check-evaluation.lean/log: terminal true/false; zero source word with false low flag; zero forward DFT; zero normalized inverse DFT; rejection of noncanonical all-one product words; an exact integer carry target equation; rejection of the same carry with zero coefficient. Outputs: true,false,true,true,true,false,true,false. These are local implementation diagnostics, not factoring-success or runtime campaigns.

The whole counter's source-layout selection/enumeration, rational exact arithmetic/storage and formal machine-composition obligations are separate. This file closes the actual local frontend/table bridge and its polynomial mathematical bit algorithm; it does not claim a completed global factorer machine-runtime theorem.
