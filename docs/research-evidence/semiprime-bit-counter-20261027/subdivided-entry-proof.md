# Complete subdivided entry endpoint

NEW SemiprimeSubdividedEntry.lean wraps the already proved original-vertex publicBitEntry and an actual two-read XOR/NOT equality circuit on the two ordered subdivision ports. publicSubdividedEntry_correct proves all-input equality to the literal subdividedTable, the table actually used by the occurrence-two public counter. publicSubdividedEntry_polynomial preserves the same public-L polynomial backend bound. Equality's five fixed charges do not require an arbitrary equality oracle.

This is the full graph-local endpoint; the previous BitCheck theorem alone concerned original Vertex entries. The paper-level preparation/flat-tape simulation extends trivially by the five-step equality case. Strict compilation and root15/all-generated audit PASS: 10 declarations, 7 theorems, only standard propext/Classical.choice/Quot.sound. Frozen earlier modules were unchanged.
