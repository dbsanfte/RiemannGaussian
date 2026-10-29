# Actual physical head histogram and original-source connector

Five new modules implement and verify the complete fixed/free head-key pass. They do not generate the old Q*n² head descriptors or compare all vertex pairs.

`SourceHistogramHeadBits.Vertex` caches an original native code and its actual compact physical key. `verticesWith` acquires it once on the actual supplied original finite list; `acquireVertices` additionally retains the paid Fin enumeration. `produce` traverses these records once. On a free interval code, it only physically increments the free counter and retains existing data: no ID or row lookup executes. On a fixed code, it physically reads the selected ID from the prefix trie once, queries the acquired row dictionary once, parses all Q colour fields, appends their actual tagged keys by a paid list-spine traversal, and physically increments the fixed counter. No native count is encoded. The result retains all query, parser, append, increment and control reports.

`acquire` calls that actual producer once and feeds its actual key list to the existing executed sparse square-histogram fold once. The returned head counters, key list, histogram trie, collision bits, and complete report are literal outputs of these operations. The materialized Q*p key list is permitted here and is counted; no compressed-list or constant-time map assumption is used.

`HeadRefinement` proves exact fixed-major original coordinate order. Actual acquired coordinate IDs and physically trimmed colour magnitudes are canonical numeric byte strings. `produce_original_keys` identifies the key list with the fixed original vertices followed by all original coordinates in order; `headKey_eq_iff` identifies byte equality with exact original (coordinate,colour) equality. Canonical numberKey/Word-valued labels are theorem specifications only, absent from the runtime path. Actual original bank validity, unit denominators, colour bounds, selected-ID membership and prefix decoder relations discharge all intermediate representations.

`HeadQueryBounds` sharpens the actual cached query to logarithmic colour fields. Original acquired colour field lengths are at most clog₂(r+1), so selected encoded rows have length at most Q*(2*clog₂(r+1)+1). The original row encoding setup still pays its raw acquisitions and trims. Subsequent one-read/all-coordinate queries satisfy the literal rowQueryBudget, including compact candidate address, selected encoded-row copy, physical field parsing and coordinate-tag construction. Produced histogram key widths are at most `2*clog₂(Q+1)+clog₂(r+1)+1`.

`HeadBounds` derives both physical counter widths from actual filtered vertex counts; common width is clog₂(N+2). For original prefix IDs from the acquired bank, actual head-pass work is at most `vs.length*vertexStage r Q V N+1`, with

```
vertexStage = 8*V +3*clog₂(r^Q+1)+12
 +rowQueryBudget r Q +3*Q+1
 +20*(clog₂(N+2)+1)+10+20.
```

The actual key count is at most Q*vs.length. The complete head-query/histogram `budget` adds the existing actual Squares budget at key width `2*clog₂(Q+1)+clog₂(r+1)+1` and count Q*N. `acquire_static_clock` discharges all variable-key and counter caps from the actual finite vertex constructor; `acquire_original_clock` specializes to the exact original finite range. Static key generation is paid separately and conservatively polynomial in n (`acquireVertices_work`); no logarithmic/near-linear setup claim is made for its native-ID encoder.

`HeadOriginal.collision_original` proves the actual returned physical collision bits equal `HeadAggregate.collisionCount` for the original baseEnvironment of the selected reverse ID prefix. `fixed_original` and `free_original` identify the actual physical counters with the original fixedVertices/freeVertices lengths. Remaining indices are exactly range' k s, and the result holds for every selected valid prefix, all k,s, empty lists, and Q=0. Skein's independently proved original_head_lane supplies the exact original H formula from this C,p,f; no C/count/truth/Fits/clock answer is a runtime argument.

All reports still use the explicit mixed physical Boolean/cell plus native finite-index/interval/control/reference model. Static original-input acquisition, persistent aliasing, full heap/pointer/tape simulation, and the final whole-public primitive-machine substitution remain distinct. These modules do not establish a new whole primitive-bit or public-rate theorem.

Strict canonical builds and ordinary-root namespace15 lint/every-generated transitive standard-three-axiom audits are recorded in histogram-head-verification.json. Independent isolated byte equality covers all five sources. A structural smoke reuses one actual r=2,Q=2 cache/prefix and checks all-fixed/mixed/all-free interval paths: (p,f,C,keyCount) are (2,0,6,4), (1,1,2,2), and (0,2,0,0). This is a branch/data diagnostic, not a factoring or scaling campaign.
