# Independent review of the six physical count/weight modules

**PASS within the explicit physical-circuit plus native-metadata scope.** Read-only review of WeightBits, WeightAcquisition, CountBitsCore, CountBitsBudget, CountBits and CountBitsBounds. No source edits or builds were performed. Final canonical and isolated object/source pins are checked in `review-physical-count-score-pins.json` against the author's final verification record.

## Actual arithmetic and acquisition

`WeightBits.weights` executes and caches seven real products: n², lambda², U², their incidence product, M² and 4M². `combine` executes the two per-candidate weighted products and their actual Boolean addition, preserving every multiplication/addition report. The incidence/head orientation is correct. The denominator-one comparator word is unconditionally valid and nonnegative; it is not made legal by an advised Fits premise.

`WeightAcquisition.acquire` constructs U by actual `unaryPower r (2Q)`, reads the acquired cell length, and executes four actual increment-based encoders for M,n,lambda,U. Runtime does not use a semantic Nat.pow to supply a bank or encoded weight. `acquire_clock` pays the bank, its length scan, every encoder and all seven products. Its width and clock majorants are polynomial in the ORIGINAL materialized dimensions, including U. This does not claim that arbitrary r^(2Q) is polynomial in its binary description. The separate helper `evaluate w I H` genuinely encodes its Nat inputs, but the final source score DOES NOT use it as a count-answer shortcut.

## No count or terminal oracle

`CountBitsCore.count` starts from the acquired Boolean terminal and accumulates actual unsigned branch words with `addBits`. It follows the same ordered alphabet recursion and `extend` override pushes as the original count. Duplicated alphabet words and repeated IDs retain their true multiplicities/override semantics. It never asks for the native count value at runtime.

`padded` executes the original active-support scan, counts those branches, actually constructs the L^(4-m) unary multiplier, encodes its acquired length, and executes a physical product. The supplied terminal is an INTERNAL generic interface: `CountBits.localCount` fixes it to the concrete `PredicateBits.terminal_original env p`, and `terminal_original_value` discharges its refinement. Neither final localCount nor score accepts a truth/count answer. Native count values in `count_value`/`padded_value` occur only in correctness specifications.

The physical `evaluate` computes each local instruction once, retains its complete report, then uses a real adder in the appropriate lane. `sequential` acquires the same prefix environment and remaining range. `score` uses those ACTUALLY produced bit lanes and cached weight words, preserving all count and weighted-circuit reports. No source rational score is decoded or evaluated to drive the new data path.

## Widths and complete callback bounds

The raw count-word bound `1+m*L` follows the actual addBits output-length recurrence, including noncanonical high-zero padding; it is not a fitted logarithm of an unknown answer. Local multiplier and output widths are derived from the actual m<=4 active-list theorem and acquired padding. Program-lane bounds add the literal number of original instructions. The common cached-weight bound and `score_width` then cover BOTH final multipliers, their output adder, and the literal denominator-one word. All arithmetic reports are for untruncated Boolean circuits.

`CountBitsBudget.TerminalCap` states bounds only at the exact reachable original environments. `count_clock` inducts over that SAME override recursion and retains all terminal/callback reports, Q-coordinate override construction, sum adders and finite branch control. Its terminal cap is discharged in `CountBitsBounds.terminal_cap` from actual original fixed-prefix/override/ID facts and the concrete predicate budget. It is not a final advised terminal cost.

`localCount_clock` covers the active scan, at most four completion levels, unary padding construction, its length scan, actual Nat-to-bits encoding, and the final multiplication. `evaluate_clock` pays every local count and every lane adder. `sequential_clock` pays prefix caching/range setup. `score_clock` additionally pays both weighted products and the final sum. The only generic cached-weight premise is actual array length, discharged by `acquire_length` at the original caller. No value/Fits/count promise is used in its place.

All source ID bounds are quantitative metadata conditions rather than execution answers. The concrete compiled-descriptor bound is available in `PredicateBitsBounds.compiled_terminal_original_work`, deriving original support IDs from the real compileAll/index enumeration. The root source-caller budget must instantiate these conditions; the six modules do not silently assert that a generic typed owner/factor/label interface is a tape-machine program.

The fixed-depth countBudget and the combined `scoreBudget_monomial` have constants independent of the original dimensions. The scalar resource cap includes the original alphabet length, program count, ID/prefix dimension, r,Q and actual cached weight width. No global 2^N assignment traversal appears: only the ACTUAL <=4 active IDs are completed.

## Scope

Boolean arithmetic, original predicate scans and physical comparator operands are acquired, with reports retained. Host natural loop/dimension representation, original finite words/types/arrays, descriptor generation and typed-label control remain the documented native metadata interfaces. The initial dimension-to-tape and complete original public controller simulation are not proved by these six modules. Callback-budget proofs are legitimate local bounds; a whole public primitive-bit theorem still needs the separate original caller/resource joins.

The authored final verification record reports strict/root15/all-generated standard3 and isolated byte equality PASS248 declarations/165 theorem constants. This review independently checks current source/object/isolated hashes against those pins and finds no mismatch. No correction is required.
