# Original source rational-word acquisition — completed

Three NEW modules; no prior source/packet edited.

## Executed input boundary

`RationalWordAcquisition.encode bits q` extracts the actual canonical numerator and positive denominator of q, then executes the existing signed integer encoder and denominator division/remainder digit loop. It emits bits+1 cells for both magnitudes, so inclusive endpoints are exact. No supplied encoded word or template is input. Validity/value require the original canonical parts fit this inclusive bound; `encode_representation` derives both bounds from a positive common denominator and common integer representation, rather than an output Fits oracle.

The actual scalar work is `8*(bits+1)+13`, with `2*(bits+1)` digit stages. This counts canonical q.num/q.den extraction, sign/absolute value, division/remainder and cells as the stated scalar operations. It is NOT a theorem implementing arbitrary rational source production or arbitrary-precision extraction on a physical bit/tape machine. The rational-to-word boundary is deliberately explicit.

`encodeArray bits J values` caches each requested encoding report once, producing exactly J physical words (zero-extending the input array). Its exact work is `J*(8*(bits+1)+13)+12*J+5`, and its complete decoded array is exactly the requested input truncation under the proved representation guards.

## Actual original source cache

`SourceWordAcquisition.acquire owner factor en eps R B` calls `MaterializedOriginalSource.acquire` ONCE, then scans the actual original incidence list and the acquired Fin n column list. Each source row is read once; every R+1 coefficient is encoded once. The output contains only cached physical words plus `sourceWork`, `encodingWork` and their joined work. Both categories remain separate. No coefficient/label/encoded-result answer is supplied.

`readSource` and `readWords` execute an actual original-incidence indexRun scan plus two stored array reads. Their cost is at most `2*M+6`; the proof matches the source idxOf ordering exactly. No free equivalence-inverse lookup is used in the physical getter. `encodingBudget M n bits R` bounds every cache traversal/encoding and retains index scans; it is a literal fixed polynomial in these dimensions. `acquire_work` retains the actual original producer report plus this encoding bound and one join operation.

The actual builtLayout integer-polynomial representation is converted by the existing proved LocalExecutionHeight source-bound lemma and instantiated with the ACTUAL OriginalSource.acquire_coefficient equality. Shared denominator is `rowDenominator Q R`; shared numerator bound is `B*2^rowNumeratorExponent Q R`. Derived `sourceBits=B+denominatorBits+rowNumeratorExponent` covers both canonical parts. Exports `acquire_row_size` (R+1), `acquire_row_valid`, `acquire_row_bounded` (sourceBits+1), `acquire_coefficient` and `acquire_representation` require only original occurrence/interpolation guards.

Runtime users must bind the returned cache once, then use readWords and retain its report. `acquiredRow` packages the logical expression for proofs; calling the whole acquire expression afresh in each callback would rerun acquisition and is not recommended or silently free. Cache getter clocks, source production and node-template acquisition must still be retained by the whole wrapper.

## Native shared width

`NativeInputBits.inputBits n B Q R J = sourceBits B Q R+n+Q+R+J+1` is the actual intended shared width. It covers sourceBits+1, is positive, and bounds n,Q,J,R, the common denominator and numerator bound by 2^b. `inputBits_le_polynomial` gives an explicit coarse fixed polynomial using clog(2,x)≤x. No template or desired intermediate fit is a premise.

## Verification and limits

Strict compile / ordinary-root fifteen linters / every generated declaration transitive standard-three-axiom audit PASS: 125 declarations, 66 theorem constants. All three isolated objects are byte-identical to canonical. Pins: rational-source-verification.json. The only structural execution controls decode -8 and 1/8 at bits=3 and run the actual one-cell original search/source/cache path; result physical decode is [[[1]]], with reports source=252, encoding=141, joined=394. These are connection diagnostics, not factoring/scaling evidence.

The source cache is now physically represented and fully initialized from actual acquired rationals. The original rational producer's internal arithmetic, scalar canonical extraction/digit operations, public descriptors, physical address simulation, and complete counter/controller bit composition are not claimed discharged by this frontend.
