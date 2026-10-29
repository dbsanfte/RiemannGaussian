# Fresh publication verification

The ordinary warning-as-error Lake build and every check in
[gates-result.json](gates-result.json) completed successfully. The
[validation record](validation.json) pins the current source inventory,
progress record, compiled dashboard and retained logs. The separate
[initial explorer review](explorer-independent-review/review.txt) covers its
original source snapshots and real desktop/mobile, file/HTTP browser behavior.
The [documentation-update review](explorer-documentation-update-review/review.txt)
independently checks the final current sources, anchors and OPEN status after
the documentation correction and regenerated explorer.
Raw terminal logs are gzip-compressed without changing their contents; the
validation record pins both compressed and uncompressed hashes.

These are fresh publication checks. They do not replace the historical FINAL
reviews, confer FINAL status on the nine drafts, or prove the open whole
original-input bit-complexity theorem. No exhaustive optional numerical
certificate rerun was performed. Historical generated-object hashes are not
asserted equal to the freshly rebuilt objects.

The initial full build compiled the individual modules but failed at the
combined root's Linux memory-mapping limit. The retained diagnostics show
65,532 mappings against a 65,530 limit, with over 48 GiB RAM available.
Raising `vm.max_map_count` to 262144 allowed the unchanged root and ordinary
build to pass. The README and CI record this setup requirement. The failed
setup attempt is retained separately from the successful build result.

The initial whole-project lint found a recursion limit in a type recheck and
three missing documentation strings. The lint command now uses the 32768
recursion allowance already used by the affected source, with every linter
enabled. Exactly three documentation comments were added to the legacy
streaming evaluator. Its [original snapshot and comparison](../source-before-documentation/manifest.json)
show that all definition, theorem and proof bodies are unchanged. The final
ordinary build and full lint include that correction.

The shared family metadata and footer update also required regenerating the
cached numerical-certificate presentation assets. Their existing proof snapshot
and certificate input audit were reused; no optional proof refresh was run.
The initial stale-asset check and regeneration log are retained. Both plot
audit records also needed regeneration to reference the current dashboard
and shared explorer audits.
The plotted formulas and figures did not change.

The staged source gate additionally passed across all indexed Lean files.
Its 15 lexical fixture tests and the 16 exact-byte whitespace fixture tests
passed. The whitespace manifest preserves only the existing 241 findings in
109 exact reviewed blobs. All 63 imported generic OpenAI modules and their
license matched the provenance hashes; reversing only their documented
import-prefix change recovered the upstream source hashes.

This record precedes the commit. The tracked pre-commit hook repeats the
required build, integrity and freshness gates, and CI independently checks
the pushed revision before deploying Pages. The deployed release record
provides that revision and workflow link.
