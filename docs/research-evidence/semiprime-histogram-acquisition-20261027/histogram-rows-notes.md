# Actual acquired candidate-row dictionary and all-coordinate queries

Three new modules join the raw-payload trie to actual original-dimension data. They contain no runtime Word-valued function, finite-colour getter, row/count lookup oracle, or provided encoded-row answer.

`SourceHistogramRows.encodeRow` reads each physical RationalWord numerator magnitude, actually trims it, and uses the executed injective `KeyBits.pair` framing onto the already encoded tail. It retains trim/frame/control reports. Its proof layout is a nested sequence of complete colour fields. A zero colour is an empty field followed by its false delimiter, so empty/prefix/zero fields do not alias. Sign and denominator are not read by this encoder: `RowKeys.original_natural` proves directly from the actual acquired colour constructor and exact row copies that every original input is unsigned with unit denominator. `original_colour_values` consequently identifies the actual trimmed magnitude fields with the actual original decoded finite coordinates. The proof-side Word decoder never executes in this path.

`zipRows` actually traverses and pairs the acquired ID and row lists, with an exact 4*pairCount+1 report. `build` acquires its tail once, encodes each row once, and physically inserts its exact encoded payload once using TrieStore.put. Original compact-bank IDs have distinct bytes and the exact ascending range order; `original_pair`, `original_nodup`, and `lookup_original` discharge the original dictionary lookup internally. No bank-row scan occurs during dictionary queries. The former linear bank reader appears only in the semantic theorem identifying the physically acquired row.

`acquireWithBank r Q` retains both the same actual compact candidate bank and the row dictionary from one shared let-bound acquisition. `RowKeys.acquireCaches r Q` adds a once-acquired compact coordinate-ID menu and retains all three setup reports. Its source.bank can serve the candidate selector, source.dictionary serves row queries, and coordinates serves every later all-coordinate parse. Calling separate acquisition definitions independently would of course pay again; the shared initializer does not do so.

With L=r^Q, B=clog₂(L+1), each actual original row has Q entries of original magnitude width at most r+1. The dictionary proves:

- encoded payload length at most Q*(2*(r+1)+1);
- node inventory at most L*(B+1);
- one-time setup at most `CompactWordBank.budget r Q L +4L+1 +L*rowStage B Q (r+1)+1+4`, where `rowStage B Q R=Q*(18R+13)+20B+28`;
- subsequent valid-ID lookup at most `8B+3*(Q*(2*(r+1)+1))+12`.

These are the actual recursive reports, including original bank generation, pairing, every frame/trim, all payload copies and trie visits. Raw framed rows are not asserted compact counters; only their proved literal payload widths are used.

`RowKeys.readKeys` performs one dictionary read and parses each encoded field once via physical split; it pairs that field with the next cached physical coordinate ID. `tag_layout`, `readKeys_original`, `readKeys_length`, `colour_key_eq_iff`, and `original_colour_values` prove exact coordinate order, exactly Q keys on the original menu, and injective coordinate/colour-key semantics. All first-field copies, split steps and framing reports remain paid. Its original closed query bound adds `Q*(6*(r+1)+6*clog₂(Q+1)+11)+8` to the dictionary lookup bound. It performs neither Q repeated bank reads nor a native finite-word query. Acquiring the compact Q coordinate IDs once adds at most `Q*(30*(clog₂(Q+1)+2)+20)+1+4` to the dictionary setup.

The clock model covers physical Boolean/cell operations and the explicitly assigned native list/constructor/reference/control stages. Existing original-bank colour/index acquisition still has its documented native loop/control interface. Immutable tail/child sharing and recursion frames are not yet lowered to a complete heap/pointer/tape machine. These results do not assert a new public primitive-bit rate or that a public caller has already switched to the dictionary.

Strict canonical compilation, ordinary RiemannGaussian-root namespace15 lint, and every generated declaration's transitive standard-three-axiom audit pass: Rows107 declarations46 theorems, RowsBounds14/11, RowKeys72/33, total193/90. Independent isolated byte equality is recorded in rows-isolated-verification.json. The one small structural smoke acquires the actual r=2,Q=2 bank/dictionary/coordinate cache and reads/tags all four physical IDs; it is not a factoring/scaling campaign.
