# Semiprime algorithm proof explorer

Open `index.html` directly, or serve the repository root and visit
`/docs/semiprime-proof-explorer/`. The Pages assembler publishes the complete
folder at `/semiprime-proof/`. There are no CDN or runtime fetch dependencies.
Source bundles load as local scripts, including under `file://`.

This is a **curated algorithm and evidence explorer**, not the existing
Lean-extracted theorem dependency graph. Source declaration locations are
parsed from authored commands. Their source text is preserved exactly;
generated/internal Lean constant names and dependency edges are not inferred.

The publication inventory supplies the source classifications and historical
focused-gate evidence. The generator validates current source hashes, cited
source declarations, evidence paths/hashes and the explicit open/paused scope.
It never invokes Lean, turns a draft into a theorem, or interprets counts as a
percentage of completion. Mathematical correctness remains separate from the
open whole primitive bit-complexity theorem. Archived external bridges are
retained as historical evidence outside the current algorithm/library.

From the repository root:

```sh
python3 scripts/build_semiprime_proof_explorer.py
python3 scripts/test_semiprime_proof_explorer.py
.lake/browser-venv/bin/python scripts/test_semiprime_proof_explorer.py --browser --refresh-preview
python3 scripts/build_semiprime_proof_explorer.py --check
```

The browser test exercises real file and HTTP previews, desktop/mobile fit,
keyboard stage navigation, search, filters, pagination and exact source lines.
The optional preview refresh records an actual Chromium screenshot and its
input/image fingerprints. `--check` validates that capture without requiring
byte-identical browser rasterization on another platform.

`data/` is generated and owned by the builder. Ordinary generation removes
obsolete generated evidence mirrors; `--check` is read-only and rejects stale
or extra generated files. Keep the folder intact when publishing. The parent
Pages assembler replaces `release.js` with the exact checked commit revision;
repository-source links are shown only when that pin is present. Local source
snapshots remain available in both versions.

After publication, the parent may check the exact deployed revision with:

```sh
.lake/browser-venv/bin/python scripts/test_semiprime_proof_explorer.py --browser \
  --url https://dbsanfte.github.io/RiemannGaussian/semiprime-proof/ \
  --expected-revision FULL_COMMIT_SHA
```

This tests the actual release revision, workflow link, source links and UI; it
does not infer a successful remote Lean workflow from a local browser test.
