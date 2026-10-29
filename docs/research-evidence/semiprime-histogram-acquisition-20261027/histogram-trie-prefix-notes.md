# Physical compact counters, trie and original-prefix acquisition

Five new modules execute actual Boolean data operations. They do not use a hash oracle, precomputed histogram/count, encoded lookup answer, or desired output Fits premise.

`SourceCompactBits.trim` removes high zeros by an actual right-recursive traversal. Value, compactness, output length and exact `6*length+1` clock are proved. Addition executes existing Boolean addition followed by that trim; increment therefore has intrinsic logarithmic output width from its actual numeric value. Physical copying is explicit.

`SourceHistogramTrie.bump` traverses one literal Boolean key path, copies the old counter once, physically increments it, and returns both that copied old counter and the persistent updated trie. Its exact numeric update theorem covers arbitrary empty and prefix keys. Compact-counter invariants derive logarithmic selected counter widths from an actual update-count cap. The clock is at most `20*key.length+30*(clog₂(M+2)+1)+30` when the actual selected old count is at most M. Quantum's concrete histogram fold derives this cap from prefix frequencies, not an encoded count oracle. Node growth is at most key length plus one. `lookup` copies its selected physical payload and stops on absent branches.

`SourceHistogramTrieStore.put` reuses the same trie but copies raw payload bytes exactly, without normalizing them. Its exact same/other-key theorem covers empty and prefix keys. The clock is at most `20*key.length+3*payload.length+21`; node growth is at most key length plus one. It preserves compact payloads when its actual inserted payload is compact, and preserves any supplied input payload-width cap. That generic map alone is not an original-input construction.

`SourceHistogramPrefix.acquire` supplies that construction for a real selected-ID prefix. It recursively acquires the tail once, trims the current input ID once, inserts at the previous actual next-key bits, and physically increments that key. Thus original key zero stores the oldest ID. `lookup_eq` proves that every compact query returns exactly `trim((fixed.reverse[bitValue query]?).getD [])`. Missing variables return the literal empty payload. The runtime does not run this proof-side reverse/numeric decoder. Compactness is necessary because trie key equality is literal byte equality; arbitrary high-zero aliases are not identified. Actual PortKeys.encodeKey is compact and has the required numerical value.

For k input IDs of original maximum width B and k≤K, actual Prefix reports satisfy

```
clock ≤ k * (100*(B+clog₂(K+2)+2)) + 1
nodes ≤ k * (clog₂(K+2)+1).
```

The generated next-key value is k and its length is at most `clog₂(k+1)`. All stored selected IDs are compact, and their lengths are bounded by the original input ID widths. No width proportional to the number of increments is used. The tail-first persistent implementation retains old child references and frames: these clocks cover visited cells, physical Boolean arithmetic, payload copies and explicitly assigned native constructor/control stages. A heap/pointer/tape implementation and global original-source/public caller substitution remain separate obligations; no full primitive-machine or public-rate result is asserted here.

Canonical strict compilation uses autoImplicit=false and warningAsError=true. Ordinary RiemannGaussian-root namespace lint and every generated declaration's transitive axiom audit pass for all five modules, allowing only propext/Classical.choice/Quot.sound: 322 declarations and 178 theorem constants. Structural smoke checks exercise empty/prefix keys, raw padded-payload preservation, compact increments, and the actual reverse-prefix constructor; these diagnostics supplement the general proofs and make no scaling claim. Isolated byte equality and exact source/object pins are recorded in `own-isolated-verification.json` and `histogram-trie-prefix-verification.json`.
