# Actual ordered macro entry execution refinement

New source: `RiemannGaussian/SemiprimeMacroEntryExecution.lean`. Frozen semantic, parameter, graph and counting files were not changed.

## Closed refinement

`binaryDecode` is executable `Nat.ofBits`. `binaryDecode_eq_sum` proves its exact little-endian binary-weight sum on the literal ordered ports. `readWord_eq_binaryDecode` removes the old noncomputable finite-equivalence inverse extensionally, for every width and Boolean input.

`explicitNormalizer depth = -2^(macroLength depth-(depth+1))` is computed by ordinary powering in the Fermat ring. The proof uses only depth+1 <= 2^(depth+1) and 2^n=-1 in Z/(2^n+1); no primality or modular-inverse oracle. It satisfies the actual length-unit equation, and `normalizer_eq_explicit` proves it equals every old Config normalizer. `executablePublicConfig` supplies this literal value and equals the entire old publicConfig, with all shape/top-width/target obligations retained.

`executableLocalPredicate` spells all actual local tests with explicit decoding and normalization: source/padding/flags; canonical forward/inverse stage words; twiddle; point multiplication; INTEGER carry relation plus strict physical carry bounds; OR and terminal checks. Its Decidable instance is constructed by vertex cases, without Classical.propDecidable. `executableEntry` uses the actual ordered `localSlotFinEquiv`, not an arbitrary scope enumeration. `executableEntry_eq_table` and `publicEntry_eq` show entrywise equality to the previously counted tensor. Thus local Boolean entries can now actually execute without the old choice-based readWord/config normalizer.

## Data-linked arithmetic work proved

`decodeRun` computes the word through its actual bit recursion, returning the same decoder result and exactly 3*width primitive bit-read/multiply/add steps. `powerRun` computes repeated multiplication with exact exponent work. `dotRun` computes a local DFT output via those actual powers/products/additions; `dotRun_value` proves precisely the local DFT sum, and `dotRun_work` proves its exact work sum. When count, stride, frequency <= n, work <= n*(n^3+2). This deliberately simple polynomial algorithm needs no FFT oracle. These are arithmetic-operation statements, not primitive bit-operation costs.

The entire `executableEntry` decider is not yet instrumented with one composed cost theorem. The decoder/DFT primitives are genuinely linked to their data paths, but their bounds have not silently been promoted into a complete Boolean entry machine theorem. Remaining refinement: compose actual entry-case scans, exponent/word work and bounded-representation ZMod/Nat arithmetic into a full polynomial bit-time/space ledger; then connect this entry implementation to the whole streamed counter implementation. No complete factoring-runtime claim follows merely from executability or finite decidability.

## Validation

Strict compile: `autoImplicit=false`, `warningAsError=true`, PASS. Root import plus all 15 scoped linters and transitive all-generated declaration axiom audit: PASS, 117 declarations / 87 theorems; only propext, Classical.choice, Quot.sound. The standard Classical.choice audit allowance does not mean the entry algorithm uses a choice evaluator: its executable definitions compile directly.

`entry-evaluation.lean` is a small execution control, not a factoring campaign: binary word 1001 decodes to 9 with 12 tracked steps; actual public input-check true/false ports return true/false; zero forward and inverse DFT blocks return true. Captured `entry-evaluation.log` contains 9, (9,12), true, false, true, true.
