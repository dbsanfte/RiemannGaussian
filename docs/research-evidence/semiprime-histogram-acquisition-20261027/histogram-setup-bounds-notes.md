# Complete actual original-input histogram setup report

NEW `SemiprimeSourceHistogramSetupBounds.lean` joins the actual `SourceHistogramSetup.acquire` call to its original-input resource bound. No implementation or frozen source is changed. This is an author scope note, not an independent review of the module.

`acquire_clock n F r Q lam arity owner hr` proves the actual setup clock is bounded by `budget n F r Q lam (sum e,arity e) (r^Q)`. Its only extra hypothesis is original r>0, already required by the actual row-bank construction bound. It has no supplied cache, row, value, record count, width, terminal callback or acquisition-work premise.

The proof retains and adds all actual reports:

1. `PortKeys.acquireOriginal`: new sparse original graph metadata and compact original owner/factor key records;
2. `RowKeys.acquireCaches`: actual original compact word bank, encoded row dictionary and compact coordinate ID list;
3. `HeadBits.verticesWith`: every original static vertex key encoder;
4. `Scales.acquire`: physical counts over the actual record/vertex lists, original r/lambda encoders/trims, powers, products, trimmed original weights;
5. `CountInput.count` over the ACTUAL metadata coordinate list, plus setup control.

Record length M=sum arity, vertex length n and coordinate length Q are proved from the actual sparse metadata producers and rewritten into the lower budget bounds. They are not cardinality inputs accepted by runtime acquisition. The final proof composes actual Nat report inequalities directly; no equality of output values substitutes a legacy clock. It does not acquire, build or ignore a hidden obsolete M²+Qn² score-term list.

The exact numeric envelope is the sum of PortKeys.budget, the full bank/row dictionary plus coordinate-ID budget, n*(keyEncoderBudget(n)+5)+1, ScalesBounds.budget, the actual coordinate count budget and8 control. Colour construction, copied rows, compact ID acquisition, physical dictionary insertion, key encodings, record scans and all scale trims remain present. It is deliberately conservative about native key/r/lambda encoders and is NOT a claim that the entire setup is near-linear in binary input length.

`budget_polynomial` and `acquire_clock_monomial` prove a fixed-family setup envelope. Constants C,k precede every original graph, arity/owner function and resource cap. Under only original positive r and original numerical caps n,F,r,Q,lambda,M=sum arity,L=r^Q<=S, actual setup clock<=C(S+1)^k. The numerical M,L caps are statements about the original input/cardinality, not advised encoded record counts or an assumed producer budget. Query-time compact widths are not weakened to the conservative setup polynomial: they remain logarithmic from the earlier actual producers.

The endpoint concerns the retained physical-bit arithmetic plus native finite metadata/list/report/control ledger. Evaluating supplied original typed arity/owner descriptors, unbounded natural control, allocation/references, full public input-to-graph construction and a literal address/tape bit-machine interpretation remain separately scoped joins. The theorem does not claim those are all paid merely because report bounds hold uniformly over typed owner functions. It supplies the concrete actual original setup report resource theorem needed by a subsequent original-query/caller composition.

Canonical strict compilation, root15/all-generated standard-three-axiom audit and separate byte-identical recompile evidence are pinned in `histogram-setup-bounds-verification.json`. No additional runtime tests are needed: this module only composes already executed producer reports and their original-value/cost theorems.
