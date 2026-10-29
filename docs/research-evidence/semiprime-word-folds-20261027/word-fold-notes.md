# Report-preserving physical word folds

NEW SemiprimeWordFoldArithmetic and SemiprimeWordFoldBounds are final frozen. Canonical strict builds, ordinary root15 lint and all-generated-declaration standard3 audits pass: 56 declarations/40 theorems and 30/27 (86/67 total). Only propext, Classical.choice and Quot.sound occur transitively. No old/frozen source, packet, journal or AGENTS file changed.

## Actual runtime API

```
zero J
one J
add template J a b
mul template J a b
scale template J a negativeBool
neg template J a
gate J testReport (body : Unit -> JetReport)
sumFrom template J f fuel start acc
sumCodes template J N (f : Fin N -> JetReport)
productList template J xs f
```

All runtime arithmetic uses RationalWord bit arrays. add/mul retain BOTH acquired reports and the actual JetBits arithmetic/copy/control report. scale chooses the literal physical integer sign, never a rational sign supplier. Gate retains the ACTUAL TestReport.work on both branches, evaluates its deferred body only on acceptance, and otherwise allocates zero. productList is the already executed native-group tail-first physical product.

sumFrom EXACTLY mirrors the frozen scalar chronological tail-recursive sum: acquire f(start) once, cache the physical add to the current accumulator, advance start and fuel. It does not regenerate old callbacks through a closure. sumCodes traverses the actual finite code interval using the same guarded Fin conversion as the existing PacketArrayExecution.sumCodes; no list of attained summaries or counts is supplied.

## Exact arithmetic and prefix invariants

add_correct, mul_correct, scale_correct and gate_correct give FULL decoded-array equality with the corresponding frozen scalar array operations/branches, plus Valid output and original common representations. Decoding is proof-side here, absent from runtime word arithmetic.

sumFrom_correct refines the exact scalar sumFrom and maintains denominator d with numerator bound

```
Bacc + fuel*B.
```

The input assumptions are ORIGINAL accumulator and callback common representations. At each executed add, both numerator fits and the next accumulator representation are derived from these assumptions and the final numeric envelope. sumFrom_prefix proves the same invariant for EVERY p<=fuel with bound Bacc+p*B. No intermediate/output Fits, final sum answer or per-prefix numerator advice occurs.

sumCodes_correct supplies the exact finite summary-code sum with output bound N*B. productList_correct reuses the actual physical native product theorem: common callback denominator D and a dyadic base N yield output denominator D^len, numerator N^(2len), Valid output and all suffix fits. The legacy callbacks in these proofs are semantic reference expressions only, not runtime rational suppliers.

sumWidth(b,fuel)=2*b+fuel+3 is a deliberately generous polynomial width. sum_numeric_bounds derives d<2^W and Bacc+fuel*B<2^W from original d,Bacc,B<=2^b. Fuel is the ACTUAL local code/head/support count; no generic global 2^n is inserted. The controller can instead use its existing sharper actual packet-width inequalities.

## Complete retained fold clocks

Bounds includes structural physical widths and exact precision sizes, then actual add_clock/mul_clock/scale_clock/gate_clock and complete finite-fold envelopes:

```
sumFrom.clock <= acc.clock + fuel*(callbackBudget + addBudget(W,J))
sumCodes.clock <= 3*J+1 + N*(callbackBudget + addBudget(W,J)).
```

Every callback, test and arithmetic report survives. Physical JetBits operation clocks and flat coefficient access/copy costs are included. Product clocks retain all same-order callback and suffix multiplication clocks. Source/table/test acquisition is NOT licensed as a unit value oracle: callers supply their actual lower reports, and correctness/clock refinements must be instantiated with concrete executed suppliers.

The scope remains the current physical-word arithmetic plus selected finite control/address ledger. Initial word/table construction, arbitrary input family getter implementation, natural clock bookkeeping and literal full memory/tape refinement require their separate joins. These folds do not by themselves prove a complete N-only primitive-bit runtime or transfer an old run.work rate to a different executor.

## Deterministic data-path control

WordFoldSmoke.lean executes a three-term signed finite sum, both gate branches and a truncated product on literal physical words. Outputs: sum #[1,-1]; rejected gate #[0,0] with clock19; accepted gate #[1,-1] with clock19 (bodyclock7 and testclock11); product #[1,-2]. Equal branch clocks in this fixture arise because zero allocation and supplied body both cost7. These are tiny algebra/compiler controls, not factoring, coverage or asymptotic evidence.
