# Root independent entry review

PASS within the stated execution-report scope. Reviewed the new entry execution,
residue-expression and whole-entry sources, with particular attention to the
actual `localRun` branches, semantic endpoints, physical bounds and preparation
note. Source hashes are captured in the packet verification data.

The arithmetic checker covers the literal source-width/flag, forward transform,
twiddle, normalized inverse transform, product, integer carry, endpoint and OR
predicates. Residues are checked canonical before guarded modular arithmetic;
malformed input words are handled, rather than assumed absent. Carry equations
use integer addition and shifts with the strict physical bounds, not only
congruence modulo the auxiliary Fermat modulus. The inverse normalization is an
explicit power/subtraction expression with a proved value.

`entryRun_correct` identifies the result with the actual ordered frozen table,
and the public endpoint specializes it using the executable public descriptor.
The report clock composes Boolean-list primitives and finite check traversals.
This is stronger than a supplied polynomial-entry oracle, but it is not the
runtime of evaluating arbitrary Lean functions for free.

Root review identified that this endpoint covers original vertices, whereas the
counter uses the equality-subdivided graph. The new `SemiprimeSubdividedEntry`
closes that exact mismatch: original entries call the existing checker, equality
entries run a literal two-bit XOR/NOT circuit, and the full subdivided table has
the same public polynomial backend bound. All port inputs remain quantified.

The preparation note explicitly pays input gathering by linear lookup, physical
modulus and public digit generation, expanded expression syntax and literal
cells. Its deliberately loose flat-tape bound is a constructive paper argument,
not an already formal compiler theorem. The published numerical constant in
that note should not be confused with the Lean-verified backend-clock constant.

No material value/normalization/guard error found. The remaining full-counter
execution composition is not inferred from the local entry result.
